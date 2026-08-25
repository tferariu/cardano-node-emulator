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

module Plutus.Examples.AccountSim where

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

type Natural = Integer

type Label = [(PubKeyHash, Value)]

type Datum = (AssetClass, Label)

data Redeemer
  = Open PubKeyHash
  | Close PubKeyHash
  | Withdraw PubKeyHash Value
  | Deposit PubKeyHash Value
  | Transfer PubKeyHash PubKeyHash Value
  | Stop

PlutusTx.unstableMakeIsData ''Redeemer
PlutusTx.makeLift ''Redeemer

type Params = ()

{-# INLINEABLE insert #-}
insert :: PubKeyHash -> Value -> Label -> Label
insert pkh val [] = [(pkh, val)]
insert pkh val ((x, y) : xs) =
  if pkh == x then (pkh, val) : xs else (x, y) : insert pkh val xs

{-# INLINEABLE delete #-}
delete :: PubKeyHash -> Label -> Label
delete pkh [] = []
delete pkh ((x, y) : xs) =
  if pkh == x then xs else (x, y) : delete pkh xs

{-# INLINEABLE lookup #-}
lookup :: PubKeyHash -> Label -> Maybe Value
lookup pkh [] = Nothing
lookup pkh ((x, y) : xs) =
  if pkh == x then Just y else lookup pkh xs

{-# INLINEABLE checkEmpty #-}
checkEmpty :: Maybe Value -> Bool
checkEmpty Nothing = False
checkEmpty (Just v) = v == emptyValue

{-# INLINEABLE checkWithdraw #-}
checkWithdraw
  :: AssetClass
  -> Maybe Value
  -> PubKeyHash
  -> Value
  -> Label
  -> ScriptContext
  -> Bool
checkWithdraw tok Nothing _ _ _ _ = False
checkWithdraw tok (Just v) pkh val map ctx =
  geq val emptyValue
    && geq v val
    && newDatum ctx
    == (tok, insert pkh (v - val) map)

{-# INLINEABLE checkDeposit #-}
checkDeposit
  :: AssetClass
  -> Maybe Value
  -> PubKeyHash
  -> Value
  -> Label
  -> ScriptContext
  -> Bool
checkDeposit tok Nothing _ _ _ _ = False
checkDeposit tok (Just v) pkh val map ctx =
  geq val emptyValue
    && newDatum ctx
    == (tok, insert pkh (v + val) map)

{-# INLINEABLE checkTransfer #-}
checkTransfer
  :: AssetClass
  -> Maybe Value
  -> Maybe Value
  -> PubKeyHash
  -> PubKeyHash
  -> Value
  -> Label
  -> ScriptContext
  -> Bool
checkTransfer tok Nothing _ _ _ _ _ _ = False
checkTransfer tok (Just vF) Nothing _ _ _ _ _ = False
checkTransfer tok (Just vF) (Just vT) from to val map ctx =
  geq val emptyValue
    && geq vF val
    && from
    /= to
    && newDatum ctx
    == (tok, insert from (vF - val) (insert to (vT + val) map))

{-# INLINEABLE agdaValidator #-}
agdaValidator
  :: Params -> Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator par (tok, map) red ctx =
  checkTokenIn tok ctx
    && case red of
      Open pkh ->
        checkTokenOut tok ctx
          && continuing ctx
          && checkSigned pkh ctx
          && isNothing (lookup pkh map)
          && newDatum ctx
          == (tok, insert pkh emptyValue map)
          && newValue ctx
          == oldValue ctx
      Close pkh ->
        checkTokenOut tok ctx
          && continuing ctx
          && checkSigned pkh ctx
          && checkEmpty (lookup pkh map)
          && newDatum ctx
          == (tok, delete pkh map)
          && newValue ctx
          == oldValue ctx
      Deposit pkh val ->
        checkTokenOut tok ctx
          && continuing ctx
          && checkSigned pkh ctx
          && checkDeposit tok (lookup pkh map) pkh val map ctx
          && newValue ctx
          == oldValue ctx
          + val
      Withdraw pkh val ->
        checkTokenOut tok ctx
          && continuing ctx
          && checkSigned pkh ctx
          && checkWithdraw tok (lookup pkh map) pkh val map ctx
          && newValue ctx
          == oldValue ctx
          - val
      Transfer from to val ->
        checkTokenOut tok ctx
          && continuing ctx
          && checkSigned from ctx
          && checkTransfer
            tok
            (lookup from map)
            (lookup to map)
            from
            to
            val
            map
            ctx
          && newValue ctx
          == oldValue ctx
      Stop ->
        checkTokenBurned tok ctx
          && not (continuing ctx)
          && map
          == []

{-# INLINEABLE checkDatum #-}
checkDatum :: Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx =
  case newDatumAddr addr ctx of
    (tok, map) -> ownAssetClass tn ctx == tok && map == []

{-# INLINEABLE checkValue #-}
checkValue :: Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx =
  checkTokenOutAddr addr (ownAssetClass tn ctx) ctx
    && newValueAddr addr ctx
    == minValue
    + assetClassValue (ownAssetClass tn ctx) 1

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
  _ -> error ()

{-# INLINEABLE validRange #-}
validRange :: ScriptContext -> Interval POSIXTime
validRange ctx = txInfoValidRange (scriptContextTxInfo ctx)

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
data AccountSim
instance Scripts.ValidatorTypes AccountSim where
  type RedeemerType AccountSim = Redeemer
  type DatumType AccountSim = Datum

smTypedValidator :: Params -> V3.TypedValidator AccountSim
smTypedValidator =
  V3.mkTypedValidatorParam @AccountSim
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
