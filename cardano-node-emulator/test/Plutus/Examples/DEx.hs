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
-- {-# OPTIONS_GHC -g -fplugin-opt PlutusTx.Plugin:coverage-all #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}

-- | A general-purpose escrow contract in Plutus
module Plutus.Examples.DEx (
  -- $multisig
  DEx,
  Label (..),
  Params (..),
  smTypedValidator,
  mkAddress,

  -- * Exposed for test endpoints
  Input (..),
  Datum,
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
  minValue,
  emptyValue,
  lovelaceValue,

  -- * testing
  writeUplc,
) where

-- writeSMValidator,
-- test,
-- test2,
-- writeCcode,
-- writeCcodePar,
-- ccode,
-- ccodePar,
-- goldenPirReadable,
-- runTestNested,
-- runTestNestedIn,
-- printPir,
-- toUPlc,
-- getPlcNoAnn,
-- writePir,
-- writeUplc,

import Control.Lens (makeClassyPrisms)
import Control.Monad (void)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.RWS.Class (asks)
import Data.Map qualified as Map

import Cardano.Api qualified as C
import Cardano.Api.Shelley qualified as C
import PlutusTx (ToData)
import PlutusTx qualified
import PlutusTx.Code (getCovIdx)
import PlutusTx.Coverage (CoverageIndex)

-- import PlutusTx.Prelude ()
-- import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Prelude hiding (ratio)
import Prelude (IO, Show (..), String, writeFile)

import Cardano.Node.Emulator qualified as E
import Cardano.Node.Emulator.Internal.Node (
  SlotConfig,
  pSlotConfig,
  posixTimeRangeToContainedSlotRange,
 )
import Cardano.Node.Emulator.Test (testnet)
import Data.Maybe (fromJust)
import Ledger (POSIXTime, PaymentPubKeyHash (unPaymentPubKeyHash), TxId, getCardanoTxId)
import Ledger qualified
import Ledger.Address (toWitness)
import Ledger.Tx.CardanoAPI qualified as C
import Ledger.Typed.Scripts (validatorCardanoAddress)
import Ledger.Typed.Scripts qualified as Scripts
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
import Plutus.Script.Utils.Value -- (Value, geq, lt)
import PlutusLedgerApi.V1.Interval qualified as Interval

import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Value qualified as V
import PlutusTx.Ratio hiding (ratio)

-- (Datum (Datum))
-- (valuePaidTo)
import PlutusLedgerApi.V2.Tx hiding (TxId) -- (OutputDatum (OutputDatum))
-- do v3..?

import PlutusLedgerApi.V3 hiding (TxId, ratio)
import PlutusLedgerApi.V3.Contexts hiding (TxId)

import Codec.Serialise (serialise)
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Short qualified as SBS
import Ledger (minAdaTxOutEstimated)
import Plutus.Script.Utils.Ada qualified as Ada
import PlutusCore.Version (plcVersion110)

import PlutusCore.Test
import PlutusTx.Test
import Test.Tasty.Extras

-- (prettyPirReadableSimple)

import Control.Exception
import Control.Lens (Getting, traverseOf, view)
import Control.Monad.Except (ExceptT, catchError, liftEither, runExceptT, throwError, withExceptT)
import Flat (Flat)
import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Pretty
import PlutusCore.Pretty qualified as PLC
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Core.Type (progTerm)
import PlutusTx.Code (CompiledCode, CompiledCodeIn, getPir, getPirNoAnn, getPlcNoAnn, sizePlc)
import Prettyprinter qualified
import Test.Tasty.Extras (TestNested, nestedGoldenVsDoc, testNested)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

{--}
{-
import PlutusLedgerApi.V2.Tx (OutputDatum (OutputDatum))
import PlutusLedgerApi.V3 (Datum (Datum))
import PlutusLedgerApi.V3.Contexts (valuePaidTo)
-}

data Info = Info {ratio :: Rational, owner :: PubKeyHash}

{-# INLINEABLE lEq #-}
lEq :: Info -> Info -> Bool
lEq l1 l2 = ratio l1 == ratio l2 && owner l1 == owner l2

instance Eq Info where
  {-# INLINEABLE (==) #-}
  b == c = lEq b c

type Label = (AssetClass, Info)

data Input
  = Update Value Rational
  | Exchange Integer PubKeyHash
  | Close
  deriving (Show)

PlutusTx.unstableMakeIsData ''Info
PlutusTx.makeLift ''Info
PlutusTx.unstableMakeIsData ''Input
PlutusTx.makeLift ''Input

-- PlutusTx.unstableMakeIsData ''State
-- PlutusTx.makeLift ''State

data Params = Params {sellC :: AssetClass, buyC :: AssetClass}
  deriving (Show)

PlutusTx.unstableMakeIsData ''Params -- ?
PlutusTx.makeLift ''Params

------------------------------------------------------------------------------------------------------------------------------
-- on-chain
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
minValue = lovelaceValue (Ada.getLovelace 3000000) -- minAdaTxOutEstimated)

{-# INLINEABLE x2MinValue #-}
x2MinValue :: Value
x2MinValue = lovelaceValue (Ada.getLovelace 6000000) -- minAdaTxOutEstimated)

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

{-# INLINEABLE checkRational #-}
checkRational :: Rational -> Bool
checkRational r = numerator r >= 0 && denominator r > 0

{-# INLINEABLE ratioCompare #-}
ratioCompare :: Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * numerator r <= b * denominator r

{-# INLINEABLE checkMinValue #-}
checkMinValue :: Value -> Bool
checkMinValue v = geq v minValue

{-# INLINEABLE getPayment #-}
getPayment :: PubKeyHash -> ScriptContext -> Value
getPayment pkh ctx = case filter
  (\i -> (txOutAddress i == (pubKeyHashAddress pkh)))
  (txInfoOutputs (scriptContextTxInfo ctx)) of
  [o] -> txOutValue o
  _ -> error ()

{-# INLINEABLE checkPaymentRatio #-}
checkPaymentRatio
  :: PubKeyHash
  -> Integer
  -> AssetClass
  -> Rational
  -> ScriptContext
  -> Bool
checkPaymentRatio pkh amt ac r ctx =
  ratioCompare amt (assetClassValueOf (getPayment pkh ctx) ac) r
    && checkMinValue (getPayment pkh ctx)

data DEx
instance Scripts.ValidatorTypes DEx where
  type RedeemerType DEx = Input
  type DatumType DEx = Label

{-# INLINEABLE agdaValidator #-}
agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator par (tok, lab) red ctx =
  checkTokenIn tok ctx
    && case red of
      Update v r ->
        checkSigned (owner lab) ctx
          && checkRational r
          && checkMinValue v
          && newValue ctx
          == v
          && newDatum ctx
          == (tok, Info r (owner lab))
          && continuing ctx
          && checkTokenOut tok ctx
      Exchange amt pkh ->
        oldValue ctx
          == newValue ctx
          + assetClassValue (sellC par) amt
          && newDatum ctx
          == (tok, lab)
          && checkPaymentRatio (owner lab) amt (buyC par) (ratio lab) ctx
          && continuing ctx
          && checkTokenOut tok ctx
      Close ->
        not (continuing ctx)
          && checkTokenBurned tok ctx
          && not (checkTokenOut tok ctx)
          && checkSigned (owner lab) ctx

smTypedValidator :: Params -> V3.TypedValidator DEx
smTypedValidator = go
  where
    go =
      V3.mkTypedValidatorParam @DEx
        $$(PlutusTx.compile [||agdaValidator||])
        $$(PlutusTx.compile [||wrap||])
    wrap = Scripts.mkUntypedValidator -- @ScriptContext @State @Input

mkAddress :: Params -> Ledger.CardanoAddress
mkAddress = validatorCardanoAddress testnet . smTypedValidator

mkOtherAddress :: Params -> Address
mkOtherAddress = V3.validatorAddress . smTypedValidator

----------------------------------------------

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

{-# INLINEABLE checkDatum #-}
checkDatum :: Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx =
  case newDatumAddr addr ctx of
    (tok, l) -> ownAssetClass tn ctx == tok && checkRational (ratio l)

{-# INLINEABLE checkValue #-}
checkValue :: Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx =
  checkTokenOutAddr addr (ownAssetClass tn ctx) ctx

{-# INLINEABLE isInitial #-}
isInitial
  :: Address -> TxOutRef -> TokenName -> ScriptContext -> Bool
isInitial addr oref tn ctx =
  consumes oref ctx
    && checkDatum addr tn ctx
    && checkValue addr tn ctx

-- Thread Token
{-# INLINEABLE agdaPolicy #-}
agdaPolicy
  :: Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
agdaPolicy addr oref tn _ ctx =
  if amt == 1
    then continuingAddr addr ctx && isInitial addr oref tn ctx
    else if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

policy :: Params -> TxOutRef -> TokenName -> V3.MintingPolicy
policy p oref tn =
  Ledger.mkMintingPolicyScript
    $ $$( PlutusTx.compile
            [||\addr' oref' tn' -> Scripts.mkUntypedMintingPolicy $ agdaPolicy addr' oref' tn'||]
        )
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 (mkOtherAddress p)
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

covIdx :: CoverageIndex
covIdx = getCovIdx $$(PlutusTx.compile [||agdaValidator||])

--------------------
{-
{-# INLINEABLE lovelaceValue #-}

-- | A 'Value' containing the given quantity of Lovelace.
lovelaceValue :: Integer -> Value
lovelaceValue = singleton adaSymbol adaToken

{-# INLINEABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces v = assetClassValueOf v (AssetClass (adaSymbol, adaToken))

-- getLovelace . fromValue

{-# INLINEABLE getVal #-}
getVal :: TxOut -> AssetClass -> Integer
getVal ip ac = assetClassValueOf (txOutValue ip) ac

-- minValue :: Value
-- minValue = lovelaceValue (Ada.getLovelace minAdaTxOutEstimated)

{-# INLINEABLE minValue #-}
minValue :: Value
minValue = lovelaceValue (Ada.getLovelace 3000000) -- minAdaTxOutEstimated)

{-# INLINEABLE emptyValue #-}
emptyValue :: Value
emptyValue = lovelaceValue (Ada.getLovelace 0)

justLovelace :: Value -> Value
justLovelace = V.lovelaceValue . V.lovelaceValueOf

{-# INLINEABLE info #-}
-- ?? needed?
info :: ScriptContext -> TxInfo
info ctx = scriptContextTxInfo ctx

{-# INLINEABLE ownInput #-}
ownInput :: ScriptContext -> TxOut
ownInput ctx = case findOwnInput ctx of
  Nothing -> error ()
  Just i -> txInInfoResolved i

{-# INLINEABLE ownOutput #-}
ownOutput :: ScriptContext -> TxOut
ownOutput ctx = case getContinuingOutputs ctx of
  [o] -> o
  _ -> traceError "oops"

{-# INLINEABLE stopsCont #-}
stopsCont :: ScriptContext -> Bool
stopsCont ctx = case getContinuingOutputs ctx of
  [] -> True
  _ -> False

{-# INLINEABLE continuing #-}
continuing :: ScriptContext -> Bool
continuing ctx = case getContinuingOutputs ctx of
  [o] -> True
  _ -> False

{-# INLINEABLE smDatum #-}
smDatum :: Maybe Datum -> Maybe State
smDatum md = do
  Datum d <- md
  PlutusTx.fromBuiltinData d

{-# INLINEABLE outputDatum #-}
outputDatum :: ScriptContext -> State
outputDatum ctx = case txOutDatum (ownOutput ctx) of
  NoOutputDatum -> error ()
  OutputDatumHash dh -> case smDatum $ findDatum dh (scriptContextTxInfo ctx) of
    Nothing -> error ()
    Just d -> d
  OutputDatum d -> PlutusTx.unsafeFromBuiltinData (getDatum d)

{-# INLINEABLE newLabel #-}
newLabel :: ScriptContext -> Label
newLabel ctx = snd (outputDatum ctx)

{-# INLINEABLE newToken #-}
newToken :: ScriptContext -> AssetClass
newToken ctx = fst (outputDatum ctx)

{-# INLINEABLE oldValue #-}
oldValue :: ScriptContext -> Value
oldValue ctx = txOutValue (ownInput ctx)

{-# INLINEABLE newValue #-}
newValue :: ScriptContext -> Value
newValue ctx = txOutValue (ownOutput ctx)

{-# INLINEABLE checkSigned #-}
checkSigned :: PubKeyHash -> ScriptContext -> Bool
checkSigned pkh ctx = txSignedBy (scriptContextTxInfo ctx) pkh

{-# INLINEABLE ratioCompare #-}
ratioCompare :: Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * numerator r <= b * denominator r

{-# INLINEABLE newDatum #-}
newDatum :: ScriptContext -> State
newDatum ctx = outputDatum ctx

{-# INLINEABLE checkTokenIn #-}
checkTokenIn :: AssetClass -> ScriptContext -> Bool
checkTokenIn ac ctx = getVal (ownInput ctx) ac == 1

{-# INLINEABLE checkTokenOut #-}
checkTokenOut :: AssetClass -> ScriptContext -> Bool
checkTokenOut ac ctx = getVal (ownOutput ctx) ac == 1

{-# INLINEABLE checkTokenBurned #-}
checkTokenBurned :: AssetClass -> ScriptContext -> Bool
checkTokenBurned ac ctx = case flattenValue (txInfoMint (scriptContextTxInfo ctx)) of
  [(cs', tn', n)]
    | cs' == fst (unAssetClass ac) && tn' == snd (unAssetClass ac) && n == -1 -> True
    | otherwise -> False
  _ -> False

--  mint ctx == (-1)

{-# INLINEABLE checkPayment #-}
{-}
checkPayment :: PaymentPubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = case filter
  (\i -> (txOutAddress i == (pubKeyHashAddress (unPaymentPubKeyHash pkh))))
  (txInfoOutputs (scriptContextTxInfo ctx)) of
  os -> any (\o -> txOutValue o == v) os-}

checkPayment :: Params -> Integer -> Label -> ScriptContext -> Bool
checkPayment par amt l ctx = case filter
  (\i -> (txOutAddress i == (pubKeyHashAddress (owner l))))
  (txInfoOutputs (scriptContextTxInfo ctx)) of
  os -> any (\o -> ratioCompare amt (assetClassValueOf (txOutValue o) (buyC par)) (rate l)) os

checkRational :: Rational -> Bool
checkRational r = (numerator r >= 0) && (denominator r > 0)
-}

ccode :: PlutusTx.CompiledCode (Params -> Label -> Input -> ScriptContext -> Bool)
ccode = $$(PlutusTx.compile [||agdaValidator||])

test :: SerialisedScript
test = serialiseCompiledCode ccode

serialisedNP :: C.PlutusScript C.PlutusScriptV3
serialisedNP = C.PlutusScriptSerialised test

writeCcode :: IO ()
writeCcode = void $ C.writeFileTextEnvelope "ccode.plutus" Nothing serialisedNP

printPir :: PlutusTx.CompiledCode a -> Doc b
printPir c = (prettyPirReadable (view progTerm (fromJust (getPirNoAnn c))))

writePir :: IO ()
writePir = writeFile "pir.txt" (show (printPir ccode))

writeUplc :: IO ()
writeUplc = writeFile "uplc.txt" (show (getPlcNoAnn ccode {--}))
