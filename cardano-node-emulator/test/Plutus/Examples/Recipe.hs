{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Plutus.Examples.Recipe where

import Cardano.Api qualified as C
import Cardano.Api.Shelley qualified as C
import Cardano.Node.Emulator qualified as E
import Cardano.Node.Emulator.Internal.Node (
  SlotConfig,
  pSlotConfig,
  posixTimeRangeToContainedSlotRange,
 )
import Cardano.Node.Emulator.Test (testnet)
import Codec.Serialise (serialise)
import Control.Exception
import Control.Lens (Getting, makeClassyPrisms, traverseOf, view)
import Control.Monad (void)
import Control.Monad.Except (ExceptT, catchError, liftEither, runExceptT, throwError, withExceptT)
import Control.Monad.RWS.Class (asks)
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Short qualified as SBS
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Flat (Flat)
import Ledger (
  POSIXTime,
  PaymentPubKeyHash (unPaymentPubKeyHash),
  TxId,
  getCardanoTxId,
  minAdaTxOutEstimated,
 )
import Ledger qualified
import Ledger.Address (toWitness)
import Ledger.Tx.CardanoAPI qualified as C
import Ledger.Typed.Scripts (validatorCardanoAddress)
import Ledger.Typed.Scripts qualified as Scripts
import Plutus.Script.Utils.Ada qualified as Ada
import Plutus.Script.Utils.Scripts (ValidatorHash, datumHash)
import Plutus.Script.Utils.V3.Contexts (
  ScriptContext (ScriptContext, scriptContextTxInfo),
  TxInfo,
  scriptOutputsAt,
  txInfoValidRange,
  txSignedBy,
 )
import Plutus.Script.Utils.V3.Scripts qualified as V3
import Plutus.Script.Utils.V3.Typed.Scripts qualified as V3
import Plutus.Script.Utils.Value
import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Pretty
import PlutusCore.Test
import PlutusCore.Version (plcVersion110)
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Core.Type
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Interval hiding (singleton)
import PlutusLedgerApi.V1.Value qualified as V
import PlutusLedgerApi.V2.Tx hiding (TxId)
import PlutusLedgerApi.V3 hiding (Datum, Redeemer, TxId, ratio)
import PlutusLedgerApi.V3 qualified as V3
import PlutusLedgerApi.V3.Contexts hiding (TxId)
import PlutusTx (ToData)
import PlutusTx qualified
import PlutusTx.Code (
  CompiledCode,
  CompiledCodeIn,
  getCovIdx,
  getPir,
  getPirNoAnn,
  getPlcNoAnn,
  sizePlc,
 )
import PlutusTx.Coverage (CoverageIndex)
import PlutusTx.Prelude hiding (ratio)
import PlutusTx.Ratio hiding (ratio)
import PlutusTx.Test
import Prettyprinter qualified
import Test.Tasty.Extras
import Test.Tasty.Extras (TestNested, nestedGoldenVsDoc, testNested)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC
import Prelude (IO, Show (..), String, writeFile)

{-# INLINEABLE validRange #-}
validRange :: ScriptContext -> Interval POSIXTime
validRange ctx = txInfoValidRange (scriptContextTxInfo ctx)

type Natural = Integer

data Label
  = Holding
  | Collecting Value PubKeyHash Integer [PubKeyHash]

PlutusTx.unstableMakeIsData ''Label
PlutusTx.makeLift ''Label

type Datum = (AssetClass, Label)

data Redeemer
  = Propose Value PubKeyHash Integer
  | Add PubKeyHash
  | Pay
  | Cancel
  | Stop

PlutusTx.unstableMakeIsData ''Redeemer
PlutusTx.makeLift ''Redeemer

data Params = Params
  { authSigs :: [PubKeyHash]
  , minSigs :: Natural
  , maxWait :: Integer
  }

PlutusTx.unstableMakeIsData ''Params
PlutusTx.makeLift ''Params

{-# INLINEABLE insert #-}
insert :: PubKeyHash -> [PubKeyHash] -> [PubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l') =
  if pkh == x then x : l' else x : insert pkh l'

{-# INLINEABLE expired #-}
expired :: Integer -> ScriptContext -> Bool
expired d ctx = before (POSIXTime d) (validRange ctx)

{-# INLINEABLE notTooLate #-}
notTooLate :: Params -> Integer -> ScriptContext -> Bool
notTooLate par d ctx =
  before (POSIXTime (d - maxWait par)) (validRange ctx)

{-# INLINEABLE agdaValidator #-}
agdaValidator
  :: Params -> Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator param (tok, lab) red ctx =
  checkTokenIn tok ctx
    && case (lab, red) of
      (Holding, Propose v pkh d) ->
        newValue ctx
          == oldValue ctx
          && geq (oldValue ctx) (v + minValue)
          && geq v minValue
          && notTooLate param d ctx
          && continuing ctx
          && checkTokenOut tok ctx
          && case newDatum ctx of
            (tok', Holding) -> False
            (tok', Collecting v' pkh' d' sigs') ->
              v
                == v'
                && pkh
                == pkh'
                && d
                == d'
                && sigs'
                == []
                && tok
                == tok'
      (Collecting v pkh d sigs, Add sig) ->
        newValue ctx
          == oldValue ctx
          && checkSigned sig ctx
          && elem sig (authSigs param)
          && continuing ctx
          && checkTokenOut tok ctx
          && case newDatum ctx of
            (tok', Holding) -> False
            ( tok'
              , Collecting v' pkh' d' sigs'
              ) ->
                v
                  == v'
                  && pkh
                  == pkh'
                  && d
                  == d'
                  && sigs'
                  == insert
                    sig
                    sigs
                  && tok
                  == tok'
      (Collecting v pkh d sigs, Pay) ->
        length sigs
          >= minSigs param
          && continuing ctx
          && checkTokenOut tok ctx
          && case newDatum ctx of
            (tok', Holding) ->
              checkPayment pkh v ctx
                && newValue ctx
                + v
                == oldValue ctx
                && tok
                == tok'
            (tok', Collecting v' pkh' d' sigs') -> False
      (Collecting v pkh d sigs, Cancel) ->
        newValue ctx
          == oldValue ctx
          && continuing ctx
          && checkTokenOut tok ctx
          && case newDatum ctx of
            (tok', Holding) ->
              expired d ctx
                && tok
                == tok'
            ( tok'
              , Collecting v' pkh' d' sigs'
              ) -> False
      (Holding, Stop) ->
        lovelaces x2MinValue
          > lovelaces (oldValue ctx)
          && not (continuing ctx)
          && checkTokenBurned tok ctx
      _ -> False

{-# INLINEABLE checkDatum #-}
checkDatum :: Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx =
  case newDatumAddr addr ctx of
    (tok, Holding) -> ownAssetClass tn ctx == tok
    (tok, Collecting _ _ _ _) -> False

{-# INLINEABLE checkValue #-}
checkValue :: Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx =
  geq (newValueAddr addr ctx) x2MinValue
    && checkTokenOutAddr addr (ownAssetClass tn ctx) ctx

{-# INLINEABLE noDups #-}
noDups :: [PubKeyHash] -> Bool
noDups [] = True
noDups (x : xs) = not (elem x xs) && noDups xs

{-# INLINEABLE checkParams #-}
checkParams :: Params -> Bool
checkParams par =
  noDups (authSigs par)
    && length (authSigs par)
    >= minSigs par
    && maxWait par
    > 0

{-# INLINEABLE agdaPolicy #-}
agdaPolicy
  :: Params
  -> Address
  -> TxOutRef
  -> TokenName
  -> ()
  -> ScriptContext
  -> Bool
agdaPolicy par addr oref tn _ ctx =
  if amt == 1
    then
      continuingAddr addr ctx
        && consumes oref ctx
        && checkDatum addr tn ctx
        && checkValue addr tn ctx
        && checkParams par
    else if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

------------------------------------------------------------------------------------------------------------------------------
-- Generic helper functions that get compiled as part of the validator
------------------------------------------------------------------------------------------------------------------------------

{-# INLINEABLE ownOutput #-}
ownOutput :: ScriptContext -> TxOut
ownOutput ctx = case getContinuingOutputs ctx of
  [o] -> o
  _ -> error ()

{-# INLINEABLE ownInput #-}
ownInput :: ScriptContext -> TxOut
ownInput ctx = case findOwnInput ctx of
  Nothing -> error ()
  Just i -> txInInfoResolved i

{-# INLINEABLE newDatum #-}
newDatum :: ScriptContext -> Datum
newDatum ctx = case txOutDatum (ownOutput ctx) of
  NoOutputDatum -> error ()
  OutputDatumHash dh -> case findDatum dh (scriptContextTxInfo ctx) of
    Nothing -> error ()
    Just d -> PlutusTx.unsafeFromBuiltinData (getDatum d)
  OutputDatum d -> PlutusTx.unsafeFromBuiltinData (getDatum d)

{-# INLINEABLE oldValue #-}
oldValue :: ScriptContext -> Value
oldValue ctx = txOutValue (ownInput ctx)

{-# INLINEABLE newValue #-}
newValue :: ScriptContext -> Value
newValue ctx = txOutValue (ownOutput ctx)

{-# INLINEABLE continuing #-}
continuing :: ScriptContext -> Bool
continuing ctx = case getContinuingOutputs ctx of
  [o] -> True
  _ -> False

{-# INLINEABLE getVal #-}
getVal :: TxOut -> AssetClass -> Integer
getVal ip ac = assetClassValueOf (txOutValue ip) ac

{-# INLINEABLE lovelaceValue #-}
lovelaceValue :: Integer -> Value
lovelaceValue = singleton adaSymbol adaToken

{-# INLINEABLE minValue #-}
minValue :: Value
minValue = lovelaceValue (Ada.getLovelace 3000000)

{-# INLINEABLE x2MinValue #-}
x2MinValue :: Value
x2MinValue = lovelaceValue (Ada.getLovelace 6000000)

{-# INLINEABLE emptyValue #-}
emptyValue :: Value
emptyValue = lovelaceValue (Ada.getLovelace 0)

{-# INLINEABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces v = assetClassValueOf v (AssetClass (adaSymbol, adaToken))

{-# INLINEABLE checkSigned #-}
checkSigned :: PubKeyHash -> ScriptContext -> Bool
checkSigned pkh ctx = txSignedBy (scriptContextTxInfo ctx) pkh

{-# INLINEABLE checkTokenIn #-}
checkTokenIn :: AssetClass -> ScriptContext -> Bool
checkTokenIn ac ctx = getVal (ownInput ctx) ac == 1

{-# INLINEABLE checkTokenOut #-}
checkTokenOut :: AssetClass -> ScriptContext -> Bool
checkTokenOut ac ctx =
  if continuing ctx
    then getVal (ownOutput ctx) ac == 1
    else False

{-# INLINEABLE checkTokenBurned #-}
checkTokenBurned :: AssetClass -> ScriptContext -> Bool
checkTokenBurned ac ctx = case flattenValue (txInfoMint (scriptContextTxInfo ctx)) of
  [(cs, _, amt)]
    | cs == (fst (unAssetClass ac)) -> amt == -1
    | otherwise -> False
  _ -> False

{-# INLINEABLE checkPayment #-}
checkPayment :: PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = case filter
  (\i -> (txOutAddress i == (pubKeyHashAddress pkh)))
  (txInfoOutputs (scriptContextTxInfo ctx)) of
  os -> any (\o -> txOutValue o == v) os

{-# INLINEABLE getPayment #-}
getPayment :: PubKeyHash -> ScriptContext -> Value
getPayment pkh ctx = case filter
  (\i -> (txOutAddress i == (pubKeyHashAddress pkh)))
  (txInfoOutputs (scriptContextTxInfo ctx)) of
  [o] -> txOutValue o
  (o : os) -> txOutValue o
  _ -> emptyValue

------------------------------------------------------------------------------------------------------------------------------
-- Generic helper functions that get compiled as part of the Minting Policy Script
------------------------------------------------------------------------------------------------------------------------------

{-# INLINEABLE getMintedAmount #-}
getMintedAmount :: ScriptContext -> Integer
getMintedAmount ctx = case flattenValue (txInfoMint (scriptContextTxInfo ctx)) of
  [(cs, _, a)]
    | cs == ownCurrencySymbol ctx -> a
    | otherwise -> 0
  _ -> 0

{-# INLINEABLE consumes #-}
consumes :: TxOutRef -> ScriptContext -> Bool
consumes oref ctx = any (\i -> txInInfoOutRef i == oref) $ txInfoInputs (scriptContextTxInfo ctx)

{-# INLINEABLE ownAssetClass #-}
ownAssetClass :: TokenName -> ScriptContext -> AssetClass
ownAssetClass tn ctx = AssetClass (ownCurrencySymbol ctx, tn)

{-# INLINEABLE outputAtAddr #-}
outputAtAddr :: Address -> ScriptContext -> TxOut
outputAtAddr addr ctx = case filter (\i -> (txOutAddress i == (addr))) (txInfoOutputs (scriptContextTxInfo ctx)) of
  [o] -> o
  _ -> error ()

{-# INLINEABLE checkTokenOutAddr #-}
checkTokenOutAddr :: Address -> AssetClass -> ScriptContext -> Bool
checkTokenOutAddr addr ac ctx = getVal (outputAtAddr addr ctx) ac == 1

{-# INLINEABLE continuingAddr #-}
continuingAddr :: Address -> ScriptContext -> Bool
continuingAddr addr ctx = case filter (\i -> (txOutAddress i == (addr))) (txInfoOutputs (scriptContextTxInfo ctx)) of
  [] -> False
  _ -> True

{-# INLINEABLE newDatumAddr #-}
newDatumAddr :: Address -> ScriptContext -> Datum
newDatumAddr addr ctx = case txOutDatum (outputAtAddr addr ctx) of
  NoOutputDatum -> error ()
  OutputDatumHash dh -> case findDatum dh (scriptContextTxInfo ctx) of
    Nothing -> error ()
    Just d -> PlutusTx.unsafeFromBuiltinData (getDatum d)
  OutputDatum d -> PlutusTx.unsafeFromBuiltinData (getDatum d)

{-# INLINEABLE newValueAddr #-}
newValueAddr :: Address -> ScriptContext -> Value
newValueAddr addr ctx = txOutValue (outputAtAddr addr ctx)

------------------------------------------------------------------------------------------------------------------------------
-- Compiling the validator
------------------------------------------------------------------------------------------------------------------------------

-- Declaring the type of the validator
data ContractName
instance Scripts.ValidatorTypes ContractName where
  type RedeemerType ContractName = Redeemer
  type DatumType ContractName = Datum

smTypedValidator :: Params -> V3.TypedValidator ContractName
smTypedValidator =
  V3.mkTypedValidatorParam @ContractName
    $$(PlutusTx.compile [||agdaValidator||])
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = Scripts.mkUntypedValidator

mkAddress :: Params -> Ledger.CardanoAddress
mkAddress = validatorCardanoAddress testnet . smTypedValidator

mkA2 :: Params -> Address
mkA2 = V3.validatorAddress . smTypedValidator

------------------------------------------------------------------------------------------------------------------------------
-- Compiling the Minting Policy Script
------------------------------------------------------------------------------------------------------------------------------

policy :: Params -> TxOutRef -> TokenName -> V3.MintingPolicy
policy p oref tn =
  Ledger.mkMintingPolicyScript
    $ $$( PlutusTx.compile
            [||\par' addr' oref' tn' -> Scripts.mkUntypedMintingPolicy $ agdaPolicy par' addr' oref' tn'||]
        )
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 p
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 (mkA2 p)
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 oref
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 tn

versionedPolicy :: Params -> TxOutRef -> TokenName -> Scripts.Versioned V3.MintingPolicy
versionedPolicy p oref tn = (Ledger.Versioned (policy p oref tn) Ledger.PlutusV3)

curSymbol' :: Params -> TxOutRef -> TokenName -> CurrencySymbol
curSymbol' p oref tn = Ledger.scriptCurrencySymbol (versionedPolicy p oref tn)

curSymbol :: Params -> TxOutRef -> TokenName -> CurrencySymbol
curSymbol p oref tn = V3.scriptCurrencySymbol (policy p oref tn)

mintingHash' :: Params -> TxOutRef -> TokenName -> Ledger.MintingPolicyHash
mintingHash' p oref tn = Ledger.mintingPolicyHash (versionedPolicy p oref tn)

mintingHash :: Params -> TxOutRef -> TokenName -> Ledger.MintingPolicyHash
mintingHash p oref tn = V3.mintingPolicyHash (policy p oref tn)

getPid :: Params -> TxOutRef -> TokenName -> Ledger.PolicyId
getPid p oref tn = Ledger.policyId (versionedPolicy p oref tn)

------------------------------------------------------------------------------------------------------------------------------
-- Code for testing
------------------------------------------------------------------------------------------------------------------------------

covIdx :: CoverageIndex
covIdx = getCovIdx $$(PlutusTx.compile [||agdaValidator||])
