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

-- | Simulating Accounts on UTxO using Plutus
module Plutus.Examples.AccountSim (
  AccountSim,
  Datum (..),
  smTypedValidator,
  mkAddress,
  insert,
  delete,
  lookup,
  emptyValue,
  minValue,

  -- * Exposed for test endpoints
  Redeemer (..),
  Datum,
  AccMap (..),
  agdaValidator,
  agdaPolicy,
  policy,
  versionedPolicy,
  curSymbol,
  mintingHash,
  getPid,

  -- * Coverage
  covIdx,

  -- * Testing
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
import PlutusIR.Core.Type (progTerm)
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Interval qualified as Interval
import PlutusLedgerApi.V1.Value qualified as V
import PlutusLedgerApi.V2.Tx hiding (TxId)
import PlutusLedgerApi.V3 hiding (Datum, Redeemer, TxId)
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
import PlutusTx.Prelude
import PlutusTx.Test
import Prettyprinter qualified
import Test.Tasty.Extras
import Test.Tasty.Extras (TestNested, nestedGoldenVsDoc, testNested)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC
import Prelude (IO, Show (..), String, writeFile)

-- Custom types for the validator

type AccMap = [(PubKeyHash, Value)]

type Datum = (AssetClass, AccMap)

data Redeemer
  = Open PubKeyHash
  | Close PubKeyHash
  | Withdraw PubKeyHash Value
  | Deposit PubKeyHash Value
  | Transfer PubKeyHash PubKeyHash Value
  | Cleanup
  deriving (Show)

-- Necessary for template Haskell and compiling the validator
PlutusTx.unstableMakeIsData ''Redeemer
PlutusTx.makeLift ''Redeemer

-- Helper functions for manipulating Account maps.
-- All functions that are part of the validator or minting policy must be inlineable for compilation
{-# INLINEABLE insert #-}
insert :: PubKeyHash -> Value -> AccMap -> AccMap
insert pkh val [] = [(pkh, val)]
insert pkh val ((x, y) : xs) =
  if pkh == x then (pkh, val) : xs else (x, y) : insert pkh val xs

{-# INLINEABLE delete #-}
delete :: PubKeyHash -> AccMap -> AccMap
delete pkh [] = []
delete pkh ((x, y) : xs) =
  if pkh == x then xs else (x, y) : delete pkh xs

{-# INLINEABLE lookup #-}
lookup :: PubKeyHash -> AccMap -> Maybe Value
lookup pkh [] = Nothing
lookup pkh ((x, y) : xs) =
  if pkh == x then Just y else lookup pkh xs

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
smDatum :: Maybe V3.Datum -> Maybe Datum
smDatum md = do
  V3.Datum d <- md
  PlutusTx.fromBuiltinData d

{-# INLINEABLE newDatum #-}
newDatum :: ScriptContext -> Datum
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

{-# INLINEABLE emptyValue #-}
emptyValue :: Value
emptyValue = lovelaceValue (Ada.getLovelace 0)

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

------------------------------------------------------------------------------------------------------------------------------
-- Contract-specific helper functions that get compiled as part of the validator
------------------------------------------------------------------------------------------------------------------------------

{-# INLINEABLE checkMembership #-}
checkMembership :: Maybe Value -> Bool
checkMembership Nothing = False
checkMembership (Just v) = True

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
  -> AccMap
  -> ScriptContext
  -> Bool
checkWithdraw tok Nothing _ _ _ _ = False
checkWithdraw tok (Just v) pkh val lab ctx =
  geq val emptyValue
    && geq v val
    && newDatum ctx
    == (tok, insert pkh (v - val) lab)

{-# INLINEABLE checkDeposit #-}
checkDeposit
  :: AssetClass
  -> Maybe Value
  -> PubKeyHash
  -> Value
  -> AccMap
  -> ScriptContext
  -> Bool
checkDeposit tok Nothing _ _ _ _ = False
checkDeposit tok (Just v) pkh val lab ctx =
  geq val emptyValue
    && newDatum ctx
    == (tok, insert pkh (v + val) lab)

{-# INLINEABLE checkTransfer #-}
checkTransfer
  :: AssetClass
  -> Maybe Value
  -> Maybe Value
  -> PubKeyHash
  -> PubKeyHash
  -> Value
  -> AccMap
  -> ScriptContext
  -> Bool
checkTransfer tok Nothing _ _ _ _ _ _ = False
checkTransfer tok (Just vF) Nothing _ _ _ _ _ = False
checkTransfer tok (Just vF) (Just vT) from to val lab ctx =
  geq val emptyValue
    && geq vF val
    && from
    /= to
    && newDatum ctx
    == (tok, insert from (vF - val) (insert to (vT + val) lab))

------------------------------------------------------------------------------------------------------------------------------
-- The Validator
------------------------------------------------------------------------------------------------------------------------------

-- Declaring the type of the validator
data AccountSim
instance Scripts.ValidatorTypes AccountSim where
  type RedeemerType AccountSim = Redeemer
  type DatumType AccountSim = Datum

{-# INLINEABLE agdaValidator #-}
agdaValidator :: Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator (tok, lab) inp ctx =
  checkTokenIn tok ctx
    && case inp of
      Open pkh ->
        checkTokenOut tok ctx
          && continuing ctx
          && checkSigned pkh ctx
          && not (isJust (lookup pkh lab))
          && newDatum ctx
          == (tok, insert pkh emptyValue lab)
          && newValue ctx
          == oldValue ctx
      Close pkh ->
        checkTokenOut tok ctx
          && continuing ctx
          && checkSigned pkh ctx
          && checkEmpty (lookup pkh lab)
          && newDatum ctx
          == (tok, delete pkh lab)
          && newValue ctx
          == oldValue ctx
      Withdraw pkh val ->
        checkTokenOut tok ctx
          && continuing ctx
          && checkSigned pkh ctx
          && checkWithdraw tok (lookup pkh lab) pkh val lab ctx
          && newValue ctx
          == oldValue ctx
          - val
      Deposit pkh val ->
        checkTokenOut tok ctx
          && continuing ctx
          && checkSigned pkh ctx
          && checkDeposit tok (lookup pkh lab) pkh val lab ctx
          && newValue ctx
          == oldValue ctx
          + val
      Transfer from to val ->
        checkTokenOut tok ctx
          && continuing ctx
          && checkSigned from ctx
          && checkTransfer
            tok
            (lookup from lab)
            (lookup to lab)
            from
            to
            val
            lab
            ctx
          && newValue ctx
          == oldValue ctx
      Cleanup ->
        checkTokenBurned tok ctx
          && not (checkTokenOut tok ctx)
          && not (continuing ctx)
          && lab
          == []

------------------------------------------------------------------------------------------------------------------------------
-- Compiling the validator
------------------------------------------------------------------------------------------------------------------------------

smTypedValidator :: V3.TypedValidator AccountSim
smTypedValidator =
  V3.mkTypedValidator @AccountSim
    $$(PlutusTx.compile [||agdaValidator||])
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = Scripts.mkUntypedValidator

mkAddress :: Ledger.CardanoAddress
mkAddress = validatorCardanoAddress testnet smTypedValidator

mkOtherAddress :: Address
mkOtherAddress = V3.validatorAddress smTypedValidator

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
  OutputDatumHash dh -> case smDatum $ findDatum dh (scriptContextTxInfo ctx) of
    Nothing -> error ()
    Just d -> d
  OutputDatum dat -> PlutusTx.unsafeFromBuiltinData @Datum (getDatum dat)

------------------------------------------------------------------------------------------------------------------------------
-- Thread Token functions that get compiled as part of the Minting Policy Script
------------------------------------------------------------------------------------------------------------------------------

{-# INLINEABLE checkDatum #-}
checkDatum :: Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx =
  case newDatumAddr addr ctx of
    (tok, map) -> ownAssetClass tn ctx == tok && map == []

{-# INLINEABLE checkValue #-}
checkValue :: Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx =
  checkTokenOutAddr addr (ownAssetClass tn ctx) ctx

{-# INLINEABLE isInitial #-}
isInitial :: Address -> TxOutRef -> TokenName -> ScriptContext -> Bool
isInitial addr oref tn ctx = consumes oref ctx && checkValue addr tn ctx && checkDatum addr tn ctx

------------------------------------------------------------------------------------------------------------------------------
-- The Minting Policy Script
------------------------------------------------------------------------------------------------------------------------------

{-# INLINEABLE agdaPolicy #-}
agdaPolicy :: Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
agdaPolicy addr oref tn _ ctx =
  if amt == 1
    then continuingAddr addr ctx && isInitial addr oref tn ctx
    else if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

------------------------------------------------------------------------------------------------------------------------------
-- Compiling the Minting Policy Script
------------------------------------------------------------------------------------------------------------------------------

policy :: TxOutRef -> TokenName -> V3.MintingPolicy
policy oref tn =
  Ledger.mkMintingPolicyScript
    $ $$( PlutusTx.compile
            [||\addr' oref' tn' -> Scripts.mkUntypedMintingPolicy $ agdaPolicy addr' oref' tn'||]
        )
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 mkOtherAddress
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 oref
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 tn

versionedPolicy :: TxOutRef -> TokenName -> Scripts.Versioned V3.MintingPolicy
versionedPolicy oref tn = (Ledger.Versioned (policy oref tn) Ledger.PlutusV3)

curSymbol' :: TxOutRef -> TokenName -> CurrencySymbol
curSymbol' oref tn = Ledger.scriptCurrencySymbol (versionedPolicy oref tn)

curSymbol :: TxOutRef -> TokenName -> CurrencySymbol
curSymbol oref tn = V3.scriptCurrencySymbol (policy oref tn)

mintingHash' :: TxOutRef -> TokenName -> Ledger.MintingPolicyHash
mintingHash' oref tn = Ledger.mintingPolicyHash (versionedPolicy oref tn)

mintingHash :: TxOutRef -> TokenName -> Ledger.MintingPolicyHash
mintingHash oref tn = V3.mintingPolicyHash (policy oref tn)

getPid :: TxOutRef -> TokenName -> Ledger.PolicyId
getPid oref tn = Ledger.policyId (versionedPolicy oref tn)

------------------------------------------------------------------------------------------------------------------------------
-- Code for testing and exporting the validator to a file
------------------------------------------------------------------------------------------------------------------------------

covIdx = getCovIdx $$(PlutusTx.compile [||agdaValidator||])
covIdx :: CoverageIndex
ccode :: PlutusTx.CompiledCode (Datum -> Redeemer -> ScriptContext -> Bool)
ccode = $$(PlutusTx.compile [||agdaValidator||])

test :: SerialisedScript
test = serialiseCompiledCode ccode

serialisedNP :: C.PlutusScript C.PlutusScriptV3
serialisedNP = C.PlutusScriptSerialised test

writeCcode :: IO ()
writeCcode = void $ C.writeFileTextEnvelope "ccodeAccountSim.plutus" Nothing serialisedNP

printPir :: PlutusTx.CompiledCode a -> Doc b
printPir c = (prettyPirReadable (view progTerm (fromJust (getPirNoAnn c))))

writePir :: IO ()
writePir = writeFile "pirAccountSim.txt" (show (printPir ccode))

writeUplc :: IO ()
writeUplc = writeFile "uplcAccountSim.txt" (show (getPlcNoAnn ccode))
