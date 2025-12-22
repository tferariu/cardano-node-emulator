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
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}

-- | A Multi-Signature Wallet contract in Plutus
module Plutus.Examples.MultiSig (
  MultiSig,
  Label (..),
  Params (..),
  smTypedValidator,
  mkAddress,
  insert,

  -- * Exposed for test endpoints
  Input (..),
  Datum,
  Natural,
  Info (..),
  agdaValidator,
  agdaPolicy,
  policy,
  versionedPolicy,
  curSymbol,
  mintingHash,
  getPid,

  -- * Coverage
  covIdx,

  -- * testing
  minValue,
  x2MinValue,
  writeUplc,
) where

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
import PlutusCore.Pretty qualified as PLC
import PlutusCore.Test
import PlutusCore.Version (plcVersion110)
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Core.Type
import PlutusIR.Core.Type (progTerm)
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Interval qualified as Interval
import PlutusLedgerApi.V1.Value qualified as V
import PlutusLedgerApi.V2.Tx hiding (TxId)
import PlutusLedgerApi.V3 hiding (TxId)
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
import PlutusTx.Prelude
import PlutusTx.Test
import Prettyprinter qualified
import Test.Tasty.Extras
import Test.Tasty.Extras (TestNested, nestedGoldenVsDoc, testNested)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC
import Prelude (IO, Show (..), String, writeFile)

-- Custom data types for the validator

type Natural = Integer

data Info
  = Holding
  | Collecting Value PubKeyHash Natural [PubKeyHash]
  deriving (Show)

-- Inlineable instance of equality needs to be defined when it cannot be derived
{-# INLINEABLE iEq #-}
iEq :: Info -> Info -> Bool
iEq Holding Holding = True
iEq Holding (Collecting _ _ _ _) = False
iEq (Collecting _ _ _ _) Holding = False
iEq (Collecting v pkh d sigs) (Collecting v' pkh' d' sigs') = v == v' && pkh == pkh' && d == d' && sigs == sigs'

instance Eq Info where
  {-# INLINEABLE (==) #-}
  b == c = iEq b c

type Label = (AssetClass, Info)

data Input
  = Propose Value PubKeyHash Natural
  | Add PubKeyHash
  | Pay
  | Cancel
  | Close
  deriving (Show)

data Params = Params
  { authSigs :: [PubKeyHash]
  , nr :: Natural
  , maxWait :: Natural
  }
  deriving (Show)

-- Necessary for template Haskell and compiling the validator
PlutusTx.unstableMakeIsData ''Info
PlutusTx.makeLift ''Info
PlutusTx.unstableMakeIsData ''Input
PlutusTx.makeLift ''Input
PlutusTx.unstableMakeIsData ''Params
PlutusTx.makeLift ''Params

-- Helper functions for processing the list of signatories.
{-# INLINEABLE query #-}
query :: PubKeyHash -> [PubKeyHash] -> Bool
query pkh [] = False
query pkh (x : l') = x == pkh || query pkh l'

{-# INLINEABLE insert #-}
insert :: PubKeyHash -> [PubKeyHash] -> [PubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l') =
  if pkh == x then x : l' else x : insert pkh l'

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

{-# INLINEABLE smDatum #-}
smDatum :: Maybe Datum -> Maybe Label
smDatum md = do
  Datum d <- md
  PlutusTx.fromBuiltinData d

{-# INLINEABLE newDatum #-}
newDatum :: ScriptContext -> Label
newDatum ctx = case txOutDatum (ownOutput ctx) of
  NoOutputDatum -> error ()
  OutputDatumHash dh -> case smDatum $ findDatum dh (scriptContextTxInfo ctx) of
    Nothing -> error ()
    Just d -> d
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

{-# INLINEABLE expired #-}
expired :: Natural -> ScriptContext -> Bool
expired d ctx = Interval.before ((POSIXTime{getPOSIXTime = d})) (txInfoValidRange (scriptContextTxInfo ctx))

{-# INLINEABLE notTooLate #-}
notTooLate :: Params -> Natural -> ScriptContext -> Bool
notTooLate par d ctx =
  Interval.before
    ((POSIXTime{getPOSIXTime = (d - maxWait par)}))
    (txInfoValidRange (scriptContextTxInfo ctx))

{-# INLINEABLE checkPayment #-}
checkPayment :: PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = case filter
  (\i -> (txOutAddress i == (pubKeyHashAddress pkh)))
  (txInfoOutputs (scriptContextTxInfo ctx)) of
  os -> any (\o -> txOutValue o == v) os

------------------------------------------------------------------------------------------------------------------------------
-- The Validator
------------------------------------------------------------------------------------------------------------------------------

-- Declaring the type of the validator
data MultiSig
instance Scripts.ValidatorTypes MultiSig where
  type RedeemerType MultiSig = Input
  type DatumType MultiSig = Label

{-# INLINEABLE agdaValidator #-}
agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param (tok, lab) red ctx =
  checkTokenIn tok ctx
    && case (checkTokenOut tok ctx, lab, red) of
      (True, Holding, Propose v pkh d) ->
        newValue ctx
          == oldValue ctx
          && geq (oldValue ctx) v
          && lovelaces v
          >= lovelaces minValue
          && notTooLate param d ctx
          && continuing ctx
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
                  == []
                  && tok
                  == tok'
      (True, Collecting v pkh d sigs, Add sig) ->
        newValue ctx
          == oldValue ctx
          && checkSigned sig ctx
          && query sig (authSigs param)
          && continuing ctx
          && case newDatum ctx of
            (tok', Holding) -> False
            ( tok'
              , Collecting
                  v'
                  pkh'
                  d'
                  sigs'
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
      (True, Collecting v pkh d sigs, Pay) ->
        length sigs
          >= nr param
          && continuing ctx
          && case newDatum ctx of
            (tok', Holding) ->
              checkPayment pkh v ctx
                && oldValue ctx
                == newValue ctx
                + v
                && tok
                == tok'
            ( tok'
              , Collecting v' pkh' d' sigs'
              ) -> False
      (True, Collecting v pkh d sigs, Cancel) ->
        newValue ctx
          == oldValue ctx
          && continuing ctx
          && case newDatum ctx of
            (tok', Holding) ->
              expired d ctx
                && tok
                == tok'
            ( tok'
              , Collecting v' pkh' d' sigs'
              ) -> False
      (False, Holding, Close) ->
        lovelaces x2MinValue
          > lovelaces (oldValue ctx)
          && not (continuing ctx)
          && checkTokenBurned tok ctx
      _ -> False

------------------------------------------------------------------------------------------------------------------------------
-- Compiling the Validator
------------------------------------------------------------------------------------------------------------------------------

smTypedValidator :: Params -> V3.TypedValidator MultiSig
smTypedValidator = go
  where
    go =
      V3.mkTypedValidatorParam @MultiSig
        $$(PlutusTx.compile [||agdaValidator||])
        $$(PlutusTx.compile [||wrap||])
    wrap = Scripts.mkUntypedValidator

mkAddress :: Params -> Ledger.CardanoAddress
mkAddress = validatorCardanoAddress testnet . smTypedValidator

mkOtherAddress :: Params -> Address
mkOtherAddress = V3.validatorAddress . smTypedValidator

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
newDatumAddr :: Address -> ScriptContext -> Label
newDatumAddr addr ctx = case txOutDatum (outputAtAddr addr ctx) of
  NoOutputDatum -> error ()
  OutputDatumHash dh -> case smDatum $ findDatum dh (scriptContextTxInfo ctx) of
    Nothing -> error ()
    Just d -> d
  OutputDatum dat -> PlutusTx.unsafeFromBuiltinData @Label (getDatum dat)

{-# INLINEABLE newValueAddr #-}
newValueAddr :: Address -> ScriptContext -> Value
newValueAddr addr ctx = txOutValue (outputAtAddr addr ctx)

------------------------------------------------------------------------------------------------------------------------------
-- Thread Token specific functions that get compiled as part of the Minting Policy Script
------------------------------------------------------------------------------------------------------------------------------

{-# INLINEABLE checkDatum #-}
checkDatum :: Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx =
  case newDatumAddr addr ctx of
    (tok, Holding) -> ownAssetClass tn ctx == tok
    (tok, Collecting _ _ _ _) -> False

{-# INLINEABLE checkValue #-}
checkValue :: Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx =
  lovelaces x2MinValue
    < lovelaces (newValueAddr addr ctx)
    && checkTokenOutAddr addr (ownAssetClass tn ctx) ctx

{-# INLINEABLE isInitial #-}
isInitial :: Address -> TokenName -> TxOutRef -> ScriptContext -> Bool
isInitial addr tn oref ctx =
  consumes oref ctx && checkDatum addr tn ctx && checkValue addr tn ctx

-- Thread Token
{-# INLINEABLE agdaPolicy #-}
agdaPolicy :: Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
agdaPolicy addr oref tn _ ctx =
  if amt == 1
    then continuingAddr addr ctx && isInitial addr tn oref ctx
    else if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

------------------------------------------------------------------------------------------------------------------------------
-- The Minting Policy Script
------------------------------------------------------------------------------------------------------------------------------

policy :: Params -> TxOutRef -> TokenName -> V3.MintingPolicy
policy p oref tn =
  Ledger.mkMintingPolicyScript
    $ $$( PlutusTx.compile
            [||\addr' oref' tn' -> Scripts.mkUntypedMintingPolicy $ agdaPolicy addr' oref' tn'||]
        )
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 (mkOtherAddress p)
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 oref
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 tn

------------------------------------------------------------------------------------------------------------------------------
-- Compiling the Minting Policy Script
------------------------------------------------------------------------------------------------------------------------------

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
-- Code for testing and exporting the validator to a file
------------------------------------------------------------------------------------------------------------------------------

covIdx :: CoverageIndex
covIdx = getCovIdx $$(PlutusTx.compile [||agdaValidator||])

ccode :: PlutusTx.CompiledCode (Params -> Label -> Input -> ScriptContext -> Bool)
ccode = $$(PlutusTx.compile [||agdaValidator||])

test :: SerialisedScript
test = serialiseCompiledCode ccode

serialisedNP :: C.PlutusScript C.PlutusScriptV3
serialisedNP = C.PlutusScriptSerialised test

writeCcode :: IO ()
writeCcode = void $ C.writeFileTextEnvelope "ccodeMultiSig.plutus" Nothing serialisedNP

printPir :: PlutusTx.CompiledCode a -> Doc b
printPir c = (prettyPirReadable (view progTerm (fromJust (getPirNoAnn c))))

writePir :: IO ()
writePir = writeFile "pirMultiSig.txt" (show (printPir ccode))

writeUplc :: IO ()
writeUplc = writeFile "uplcMultiSig.txt" (show (getPlcNoAnn ccode {--}))
