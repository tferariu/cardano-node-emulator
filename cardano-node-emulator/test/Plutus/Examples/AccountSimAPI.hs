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

-- {-# OPTIONS_GHC -g -fplugin-opt PlutusTx.Plugin:coverage-all #-}

-- {-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}

-- | A general-purpose escrow contract in Plutus
module Plutus.Examples.AccountSimAPI (
  -- * Actions
  start,
  open,
  close,
  withdraw,
  deposit,
  transfer,
  cleanup,
  TxSuccess (..),
  -- mkStartTx',
) where

import Control.Lens (makeClassyPrisms)
import Control.Monad (void, when)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.RWS.Class (asks)
import Data.Map qualified as Map

import Cardano.Api qualified as C
import Cardano.Api.Shelley qualified as C
import PlutusTx (ToData)
import PlutusTx qualified
import PlutusTx.Code (getCovIdx)
import PlutusTx.Coverage (CoverageIndex)

import PlutusTx.Prelude (traceError, traceIfFalse)
import PlutusTx.Prelude qualified as PlutusTx

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
import Plutus.Script.Utils.V3.Typed.Scripts qualified as V3
import Plutus.Script.Utils.Value -- (Value, geq, lt)
import PlutusLedgerApi.V1.Interval qualified as Interval

import PlutusLedgerApi.V1.Address

-- (Datum (Datum))
-- (Datum (Datum))
-- (valuePaidTo)
import PlutusLedgerApi.V2.Tx hiding (TxId) -- (OutputDatum (OutputDatum))
{-
import PlutusLedgerApi.V2.Tx (OutputDatum (OutputDatum))
import PlutusLedgerApi.V3 (Datum (Datum))
import PlutusLedgerApi.V3.Contexts (valuePaidTo)
-}

import PlutusLedgerApi.V3 hiding (TxId)
import PlutusLedgerApi.V3.Contexts hiding (TxId)

import Ledger (minAdaTxOutEstimated)
import Ledger.Address (toWitness)
import Plutus.Script.Utils.V1.Scripts qualified as Script

import Plutus.Examples.AccountSim
import Plutus.Script.Utils.Value
import PlutusLedgerApi.V1.Value qualified as V

import Debug.Trace

-- import Cardano.Ledger.Alonzo.Plutus.TxInfo (transPolicyID)

toTxOutValue :: Value -> C.TxOutValue C.ConwayEra
toTxOutValue = either (error . show) C.toCardanoTxOutValue . C.toCardanoValue

toPolicyId :: Ledger.MintingPolicyHash -> Ledger.PolicyId
toPolicyId = either (error . show) id . C.toCardanoPolicyId

toAssetId :: AssetClass -> Ledger.AssetId
toAssetId = either (error . show) id . C.toCardanoAssetId

toTxIn :: TxOutRef -> C.TxIn
toTxIn = either (error . show) id . C.toCardanoTxIn

toLedgerValue :: Value -> Ledger.Value
toLedgerValue = either (error . show) id . C.toCardanoValue

toHashableScriptData :: (PlutusTx.ToData a) => a -> C.HashableScriptData
toHashableScriptData = C.unsafeHashableScriptData . C.fromPlutusData . PlutusTx.toData

toTxOutInlineDatum :: (PlutusTx.ToData a) => a -> C.TxOutDatum C.CtxTx C.ConwayEra
toTxOutInlineDatum = C.TxOutDatumInline C.BabbageEraOnwardsConway . toHashableScriptData

toValidityRange
  :: SlotConfig
  -> Interval.Interval POSIXTime
  -> (C.TxValidityLowerBound C.ConwayEra, C.TxValidityUpperBound C.ConwayEra)
toValidityRange slotConfig =
  either (error . show) id . C.toCardanoValidityRange . posixTimeRangeToContainedSlotRange slotConfig

alwaysSucceedPolicy :: V3.MintingPolicy
alwaysSucceedPolicy =
  Ledger.MintingPolicy (C.fromCardanoPlutusScript $ C.examplePlutusScriptAlwaysSucceeds C.WitCtxMint)

alwaysSucceedPolicyId :: C.PolicyId
alwaysSucceedPolicyId =
  C.scriptPolicyId
    (C.PlutusScript C.PlutusScriptV1 $ C.examplePlutusScriptAlwaysSucceeds C.WitCtxMint)

someTokenValue :: C.AssetName -> Integer -> C.Value
someTokenValue an i = C.valueFromList [(C.AssetId alwaysSucceedPolicyId an, C.Quantity i)]

threadTokenValue :: TxOutRef -> TokenName -> C.AssetName -> C.Value
threadTokenValue oref tn an = C.valueFromList [(C.AssetId (getPid oref tn) an, C.Quantity 1)]

burnTokenValue :: TxOutRef -> TokenName -> C.AssetName -> C.Value
burnTokenValue oref tn an = C.valueFromList [(C.AssetId (getPid oref tn) an, C.Quantity (-1))]

burnTokenValue' :: AssetClass -> C.Value
burnTokenValue' ac = C.valueFromList [(toAssetId ac, C.Quantity (-1))]

lovelaces :: Value -> Integer
lovelaces v = assetClassValueOf v (AssetClass (adaSymbol, adaToken))

getLargest
  :: TxOutRef
  -> Ledger.DecoratedTxOut
  -> (TxOutRef, Ledger.DecoratedTxOut)
  -> (TxOutRef, Ledger.DecoratedTxOut)
-- Map C.TxIn (C.TxOut C.CtxUTxO C.ConwayEra) -> C.TxIn
getLargest k v (ix, max) =
  if lovelaces (C.fromCardanoValue (Ledger._decoratedTxOutValue v))
    >= lovelaces (C.fromCardanoValue (Ledger._decoratedTxOutValue max))
    then (k, v)
    else (ix, max)

mkStartTx
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex, TxOutRef, C.TxIn)
mkStartTx wallet = do
  slotConfig <- asks pSlotConfig
  unspentOutputs <- E.utxosAt wallet
  uO <- E.utxosAtPlutus wallet

  let oref = fst (Map.foldrWithKey getLargest ((head (Map.keys uO)), (head (Map.elems uO))) uO)
      tin = toTxIn oref

  let utxos = Map.toList (C.unUTxO unspentOutputs)

  when (length (utxos) == 0) $
    throwError $
      E.CustomError $
        "no UTxOs"

  let utxo = head utxos

  let tn = "ThreadToken"
      an = "ThreadToken"
      cs = curSymbol oref tn
      tt = assetClass cs tn

  let smAddress = mkAddress
      txOut =
        C.TxOut
          smAddress
          (toTxOutValue (minValue <> assetClassValue tt 1))
          (toTxOutInlineDatum @Label (tt, []))
          C.ReferenceScriptNone
      validityRange = toValidityRange slotConfig $ Interval.always

  let mintValue = threadTokenValue oref tn an
      redeemer = Redeemer (toBuiltinData ())

  let mintWitness =
        either (error . show) id $
          C.toCardanoMintWitness redeemer Nothing (Just (versionedPolicy oref tn))

  -- traceShowM $ tin

  let txMintValue =
        C.TxMintValue
          C.MaryEraOnwardsConway
          (mintValue)
          (C.BuildTxWith (Map.singleton (getPid oref tn) mintWitness))

      utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          , C.txMintValue = txMintValue
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          }
      utxoIndex = mempty
   in pure (C.CardanoBuildTx utx, utxoIndex, oref, tin)

newtype TxSuccess = TxSuccess TxId
  deriving (Eq, Show)

newtype StartSuccess = StartSuccess TxOutRef
  deriving (Eq, Show)

start
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -- -> AssetClass
  -> m (TxOutRef, C.TxIn)
start wallet privateKey = do
  E.logInfo @String $ "Starting"
  (utx, utxoIndex, oref, tin) <- mkStartTx wallet
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx
  return (oref, tin)

cardanoTxOutDatum :: forall d. (FromData d) => C.TxOut C.CtxUTxO C.ConwayEra -> Maybe d
cardanoTxOutDatum (C.TxOut _aie _tov tod _rs) =
  case tod of
    C.TxOutDatumNone ->
      Nothing
    C.TxOutDatumHash _era _scriptDataHash ->
      Nothing
    C.TxOutDatumInline _era scriptData ->
      fromData @d $ C.toPlutusData $ C.getScriptData scriptData

toPkhAddress :: PaymentPubKeyHash -> Ledger.CardanoAddress
toPkhAddress pkh =
  C.makeShelleyAddressInEra
    C.shelleyBasedEra
    testnet
    (either (error . show) C.PaymentCredentialByKey $ C.toCardanoPaymentKeyHash pkh)
    C.NoStakeAddress

mkOpenTx
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkOpenTx wallet tt = do
  let smAddress = mkAddress
      pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  let
    validUnspentOutputs =
      Map.filter
        ( \(C.TxOut _aie tov _tod _rs) ->
            ( assetClassValueOf
                (C.fromCardanoValue (C.fromCardanoTxOutValue tov))
                tt
                == 1
            )
        )
        $ C.unUTxO unspentOutputs

  when (length (validUnspentOutputs) == 0) $
    throwError $
      E.CustomError $
        ("found no SM but: " ++ (show unspentOutputs))
  {-( show (map (\(C.TxOut _aie tov _tod _rs) ->
      tov ) $ Map.elems (C.unUTxO unspentOutputs) )))-}
  when (length (validUnspentOutputs) > 1) $
    throwError $
      E.CustomError $
        "found too many SM"
  --  when (length (validUnspentOutputs) /= 1) $
  --    throwError $
  --      E.CustomError $
  --        "not SM"

  let
    -- currentlyLocked = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue (C.unUTxO unspentOutputs)) --old
    remainingValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
    datums = map (cardanoTxOutDatum @Label) (Map.elems validUnspentOutputs)
    datum = case datums of
      (Just (tt', label)) : _ -> (tt', (insert (unPaymentPubKeyHash pkh) emptyValue label))
      -- State{label = Collecting v pkh' d (insert pkh sigs), tToken = tt}
      otherwise -> (tt, [])

    -- datum = State {label = Holding, tToken = tt}
    -- newDatum = C.unsafeHashableScriptData $ C.fromPlutusData $ PlutusTx.toData $
    --            (State {label = Collecting val pkh d [], tToken = tt})
    -- get actual datum!!
    remainingOutputs =
      [C.TxOut smAddress (toTxOutValue remainingValue) (toTxOutInlineDatum datum) C.ReferenceScriptNone]

    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Open (unPaymentPubKeyHash pkh))
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator))
    witness =
      C.BuildTxWith $
        C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits

    txIns = (,witness) <$> Map.keys validUnspentOutputs

    utx =
      E.emptyTxBodyContent
        { C.txIns = txIns
        , C.txOuts = remainingOutputs
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsConway [extraKeyWit]
        }
   in
    pure (C.CardanoBuildTx utx, unspentOutputs)

open
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> AssetClass
  -> m TxSuccess
open wallet privateKey tt = do
  E.logInfo @String "Opening"
  (utx, utxoIndex) <- mkOpenTx wallet tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

mkCloseTx
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkCloseTx wallet tt = do
  let smAddress = mkAddress
      pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  let
    validUnspentOutputs =
      Map.filter
        ( \(C.TxOut _aie tov _tod _rs) ->
            ( assetClassValueOf
                (C.fromCardanoValue (C.fromCardanoTxOutValue tov))
                tt
                == 1
            )
        )
        $ C.unUTxO unspentOutputs
  when (length (validUnspentOutputs) /= 1) $
    throwError $
      E.CustomError $
        "not SM"

  let
    -- currentlyLocked = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue (C.unUTxO unspentOutputs)) --old
    remainingValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
    datums = map (cardanoTxOutDatum @Label) (Map.elems validUnspentOutputs)
    datum = case datums of
      (Just (tt', label)) : _ -> (tt', (delete (unPaymentPubKeyHash pkh) label))
      -- State{label = Collecting v pkh' d (insert pkh sigs), tToken = tt}
      otherwise -> (tt, [])

    -- datum = State {label = Holding, tToken = tt}
    -- newDatum = C.unsafeHashableScriptData $ C.fromPlutusData $ PlutusTx.toData $
    --            (State {label = Collecting val pkh d [], tToken = tt})
    -- get actual datum!!
    remainingOutputs =
      [C.TxOut smAddress (toTxOutValue remainingValue) (toTxOutInlineDatum datum) C.ReferenceScriptNone]

    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Close (unPaymentPubKeyHash pkh))
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator))
    witness =
      C.BuildTxWith $
        C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits

    txIns = (,witness) <$> Map.keys validUnspentOutputs

    utx =
      E.emptyTxBodyContent
        { C.txIns = txIns
        , C.txOuts = remainingOutputs
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsConway [extraKeyWit]
        }
   in
    pure (C.CardanoBuildTx utx, unspentOutputs)

close
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> AssetClass
  -> m TxSuccess
close wallet privateKey tt = do
  E.logInfo @String "Closing"
  (utx, utxoIndex) <- mkCloseTx wallet tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

mkWithdrawTx
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Value
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkWithdrawTx wallet val tt = do
  let smAddress = mkAddress
      pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  let
    validUnspentOutputs =
      Map.filter
        ( \(C.TxOut _aie tov _tod _rs) ->
            ( assetClassValueOf
                (C.fromCardanoValue (C.fromCardanoTxOutValue tov))
                tt
                == 1
            )
        )
        $ C.unUTxO unspentOutputs
  when (length (validUnspentOutputs) /= 1) $
    throwError $
      E.CustomError $
        "not SM"

  let
    remainingValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
    datums = map (cardanoTxOutDatum @Label) (Map.elems validUnspentOutputs)
    datum = case datums of
      (Just (tt', label)) : _ ->
        ( case (Plutus.Examples.AccountSim.lookup (unPaymentPubKeyHash pkh) label) of
            Just v -> (tt', (insert (unPaymentPubKeyHash pkh) (v PlutusTx.- val) label))
            Nothing -> (tt, [])
        )
      -- State{label = Collecting v pkh' d (insert pkh sigs), tToken = tt}
      otherwise -> (tt, [])

    -- datum = State {label = Holding, tToken = tt}
    -- newDatum = C.unsafeHashableScriptData $ C.fromPlutusData $ PlutusTx.toData $
    --            (State {label = Collecting val pkh d [], tToken = tt})
    -- get actual datum!!
    remainingOutputs =
      [ C.TxOut
          smAddress
          (toTxOutValue (remainingValue <> (PlutusTx.negate val)))
          (toTxOutInlineDatum datum)
          C.ReferenceScriptNone
      ]

    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Withdraw (unPaymentPubKeyHash pkh) val)
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator))
    witness =
      C.BuildTxWith $
        C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits

    txIns = (,witness) <$> Map.keys validUnspentOutputs

    utx =
      E.emptyTxBodyContent
        { C.txIns = txIns
        , C.txOuts = remainingOutputs
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsConway [extraKeyWit]
        }
   in
    pure (C.CardanoBuildTx utx, unspentOutputs)

withdraw
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Value
  -> AssetClass
  -> m TxSuccess
withdraw wallet privateKey val tt = do
  E.logInfo @String "Withdrawing"
  (utx, utxoIndex) <- mkWithdrawTx wallet val tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

mkDepositTx
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Value
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkDepositTx wallet val tt = do
  let smAddress = mkAddress
      pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  let
    validUnspentOutputs =
      Map.filter
        ( \(C.TxOut _aie tov _tod _rs) ->
            ( assetClassValueOf
                (C.fromCardanoValue (C.fromCardanoTxOutValue tov))
                tt
                == 1
            )
        )
        $ C.unUTxO unspentOutputs
  when (length (validUnspentOutputs) /= 1) $
    throwError $
      E.CustomError $
        "not SM"

  {-
    when (length (validUnspentOutputs) == 1) $
      throwError $
        E.CustomError $
          "test"        -}

  let
    -- currentlyLocked = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue (C.unUTxO unspentOutputs)) --old
    remainingValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
    datums = map (cardanoTxOutDatum @Label) (Map.elems validUnspentOutputs)
    datum = case datums of
      (Just (tt', label)) : _ ->
        ( case (Plutus.Examples.AccountSim.lookup (unPaymentPubKeyHash pkh) label) of
            Just v -> (tt', (insert (unPaymentPubKeyHash pkh) (v PlutusTx.+ val) label))
            Nothing -> (tt, [])
        )
      -- State{label = Collecting v pkh' d (insert pkh sigs), tToken = tt}
      otherwise -> (tt, [])

    -- datum = State {label = Holding, tToken = tt}
    -- newDatum = C.unsafeHashableScriptData $ C.fromPlutusData $ PlutusTx.toData $
    --            (State {label = Collecting val pkh d [], tToken = tt})
    -- get actual datum!!
    remainingOutputs =
      [ C.TxOut
          smAddress
          (toTxOutValue (remainingValue <> val))
          (toTxOutInlineDatum datum)
          C.ReferenceScriptNone
      ]

    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Deposit (unPaymentPubKeyHash pkh) val)
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator))
    witness =
      C.BuildTxWith $
        C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits

    txIns = (,witness) <$> Map.keys validUnspentOutputs

    utx =
      E.emptyTxBodyContent
        { C.txIns = txIns
        , C.txOuts = remainingOutputs
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsConway [extraKeyWit]
        }
   in
    pure (C.CardanoBuildTx utx, unspentOutputs)

deposit
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Value
  -> AssetClass
  -> m TxSuccess
deposit wallet privateKey val tt = do
  E.logInfo @String ("Depositing " ++ (show val))
  (utx, utxoIndex) <- mkDepositTx wallet val tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

mkTransferTx
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.CardanoAddress
  -> Value
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkTransferTx wallet wallet' val tt = do
  let smAddress = mkAddress
      pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
      pkh' = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet'
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  let
    validUnspentOutputs =
      Map.filter
        ( \(C.TxOut _aie tov _tod _rs) ->
            ( assetClassValueOf
                (C.fromCardanoValue (C.fromCardanoTxOutValue tov))
                tt
                == 1
            )
        )
        $ C.unUTxO unspentOutputs
  when (length (validUnspentOutputs) /= 1) $
    throwError $
      E.CustomError $
        "not SM"
  let
    -- currentlyLocked = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue (C.unUTxO unspentOutputs)) --old
    remainingValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
    datums = map (cardanoTxOutDatum @Label) (Map.elems validUnspentOutputs)
    (tt', label) = case datums of
      (Just (tt', label)) : _ -> (tt', label)
      -- State{label = Collecting v pkh' d (insert pkh sigs), tToken = tt}
      otherwise -> (tt, [])
    vF = case (Plutus.Examples.AccountSim.lookup (unPaymentPubKeyHash pkh) label) of
      Just v -> v
      Nothing -> emptyValue
    vT = case (Plutus.Examples.AccountSim.lookup (unPaymentPubKeyHash pkh') label) of
      Just v -> v
      Nothing -> emptyValue
    datum =
      ( tt'
      , ( insert
            (unPaymentPubKeyHash pkh)
            (vF PlutusTx.- val)
            (insert (unPaymentPubKeyHash pkh') (vT PlutusTx.+ val) label)
        )
      )

    -- datum = State {label = Holding, tToken = tt}
    -- newDatum = C.unsafeHashableScriptData $ C.fromPlutusData $ PlutusTx.toData $
    --            (State {label = Collecting val pkh d [], tToken = tt})
    -- get actual datum!!
    remainingOutputs =
      [C.TxOut smAddress (toTxOutValue remainingValue) (toTxOutInlineDatum datum) C.ReferenceScriptNone]

    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Transfer (unPaymentPubKeyHash pkh) (unPaymentPubKeyHash pkh') val)
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator))
    witness =
      C.BuildTxWith $
        C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits

    txIns = (,witness) <$> Map.keys validUnspentOutputs

    utx =
      E.emptyTxBodyContent
        { C.txIns = txIns
        , C.txOuts = remainingOutputs
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsConway [extraKeyWit]
        }
   in
    pure (C.CardanoBuildTx utx, unspentOutputs)

transfer
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Value
  -> AssetClass
  -> m TxSuccess
transfer wallet wallet' privateKey val tt = do
  E.logInfo @String "Transferring"
  (utx, utxoIndex) <- mkTransferTx wallet wallet' val tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

mkCleanupTx
  :: (E.MonadEmulator m)
  => AssetClass
  -> C.TxIn
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkCleanupTx tt tin = do
  let smAddress = mkAddress
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  let
    validUnspentOutputs =
      Map.filter
        ( \(C.TxOut _aie tov _tod _rs) ->
            ( assetClassValueOf
                (C.fromCardanoValue (C.fromCardanoTxOutValue tov))
                tt
                == 1
            )
        )
        $ C.unUTxO unspentOutputs
    currentValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
  when (length (validUnspentOutputs) /= 1) $
    throwError $
      E.CustomError $
        "not SM"

  let
    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Cleanup)
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator))
    witness =
      C.BuildTxWith $
        C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
    txIns = (,witness) <$> Map.keys validUnspentOutputs

  let
    tn = "ThreadToken"
    an = "ThreadToken"
    oref = C.fromCardanoTxIn tin
    mintValue = burnTokenValue oref tn an
    mintWitness =
      either (error . show) id $
        C.toCardanoMintWitness (Redeemer (toBuiltinData ())) Nothing (Just (versionedPolicy oref tn))
    txMintValue =
      C.TxMintValue
        C.MaryEraOnwardsConway
        (mintValue)
        (C.BuildTxWith (Map.singleton (getPid oref tn) mintWitness {--}))
        -- (toPolicyId (currencyMPSHash (fst (unAssetClass tt))))
    utx =
      E.emptyTxBodyContent
        { C.txIns = txIns
        , -- , C.txOuts = remainingOutputs
          C.txMintValue = txMintValue
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        }
   in
    pure (C.CardanoBuildTx utx, unspentOutputs)

cleanup
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> AssetClass
  -> C.TxIn
  -> m TxSuccess
cleanup wallet privateKey tt tin = do
  E.logInfo @String "Closing"
  (utx, utxoIndex) <- mkCleanupTx tt tin
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

{-
mkOpenTx
  :: (E.MonadEmulator m)
  => PaymentPubKeyHash
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkOpenTx pkh tt = do
  let smAddress = mkAddress
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  let
    validUnspentOutputs' =
      Map.filter
        ( \(C.TxOut _aie tov _tod _rs) ->
            ( assetClassValueOf
                (C.fromCardanoValue (C.fromCardanoTxOutValue tov))
                tt
                == 1
            )
        )
        $ C.unUTxO unspentOutputs

  {-when (length (validUnspentOutputs') /= 1)
    $ throwError $ E.CustomError $ "not SM" -}
  when (length (validUnspentOutputs') == 0) $
    throwError $
      E.CustomError $
        ("found no SM but: " ++ (show unspentOutputs))
  {-( show (map (\(C.TxOut _aie tov _tod _rs) ->
      tov ) $ Map.elems (C.unUTxO unspentOutputs) )))-}
  when (length (validUnspentOutputs') > 1) $
    throwError $
      E.CustomError $
        "found too many SM"
  let
    -- currentlyLocked = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue (C.unUTxO unspentOutputs)) --old
    remainingValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs')
    datum = (tt , (insert pkh ))
    -- newDatum = C.unsafeHashableScriptData $ C.fromPlutusData $ PlutusTx.toData $
    --            (State {label = Collecting val pkh d [], tToken = tt})
    -- get actual datum!!
    remainingOutputs =
      [C.TxOut smAddress (toTxOutValue remainingValue) (toTxOutInlineDatum datum) C.ReferenceScriptNone]

    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Propose val pkh d)
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
    witness =
      C.BuildTxWith $
        C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits

    txIns = (,witness) <$> Map.keys validUnspentOutputs'

    utx =
      E.emptyTxBodyContent
        { C.txIns = txIns
        , C.txOuts = remainingOutputs
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        }
   in
    pure (C.CardanoBuildTx utx, unspentOutputs)

propose
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> Value
  -> PaymentPubKeyHash
  -> Deadline
  -> AssetClass
  -> m TxSuccess
propose wallet privateKey params val pkh d tt = do
  E.logInfo @String "Proposing"
  (utx, utxoIndex) <- mkProposeTx params val pkh d tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx
-}
