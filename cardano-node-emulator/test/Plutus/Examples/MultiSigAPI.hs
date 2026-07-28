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

-- | Off-chain code for the Multi-signature wallet
module Plutus.Examples.MultiSigAPI (
  -- * Actions
  propose,
  add,
  pay,
  cancel,
  start,
  stop,
  TxSuccess (..),
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
import Control.Lens (makeClassyPrisms)
import Control.Monad (void, when)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.RWS.Class (asks)
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Debug.Trace
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
import Plutus.Examples.MultiSig
import Plutus.Script.Utils.Scripts (ValidatorHash, datumHash)
import Plutus.Script.Utils.V1.Scripts qualified as Script
import Plutus.Script.Utils.V3.Contexts (
  ScriptContext (ScriptContext, scriptContextTxInfo),
  TxInfo,
  scriptOutputsAt,
  txInfoValidRange,
  txSignedBy,
 )
import Plutus.Script.Utils.V3.Typed.Scripts qualified as V3
import Plutus.Script.Utils.Value
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Interval qualified as Interval
import PlutusLedgerApi.V2.Tx hiding (TxId)
import PlutusLedgerApi.V3 hiding (Datum, Redeemer, TxId)
import PlutusLedgerApi.V3 qualified as V3
import PlutusLedgerApi.V3.Contexts hiding (TxId)
import PlutusTx (ToData)
import PlutusTx qualified
import PlutusTx.Code (getCovIdx)
import PlutusTx.Coverage (CoverageIndex)
import PlutusTx.Prelude (traceError, traceIfFalse)
import PlutusTx.Prelude qualified as PlutusTx

------------------------------------------------------------------------------------------------------------------------------
-- Helper functions for translating between types and getting desired components
------------------------------------------------------------------------------------------------------------------------------

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

threadTokenValue :: Params -> TxOutRef -> TokenName -> C.AssetName -> C.Value
threadTokenValue p oref tn an = C.valueFromList [(C.AssetId (getPid p oref tn) an, C.Quantity 1)]

burnTokenValue :: Params -> TxOutRef -> TokenName -> C.AssetName -> C.Value
burnTokenValue p oref tn an = C.valueFromList [(C.AssetId (getPid p oref tn) an, C.Quantity (-1))]

burnTokenValue' :: AssetClass -> C.Value
burnTokenValue' ac = C.valueFromList [(toAssetId ac, C.Quantity (-1))]

lovelaces :: Value -> Integer
lovelaces v = assetClassValueOf v (AssetClass (adaSymbol, adaToken))

newtype TxSuccess = TxSuccess TxId
  deriving (Eq, Show)

getLargest
  :: TxOutRef
  -> Ledger.DecoratedTxOut
  -> (TxOutRef, Ledger.DecoratedTxOut)
  -> (TxOutRef, Ledger.DecoratedTxOut)
getLargest k v (ix, max) =
  if lovelaces (C.fromCardanoValue (Ledger._decoratedTxOutValue v))
    >= lovelaces (C.fromCardanoValue (Ledger._decoratedTxOutValue max))
    then (k, v)
    else (ix, max)

-- traceShowM $ debug -- for debugging

------------------------------------------------------------------------------------------------------------------------------
-- Building and submitting the transactions
------------------------------------------------------------------------------------------------------------------------------

mkStartTx
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> Value
  -> Bool
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex, TxOutRef, C.TxIn, (C.TxOut C.CtxUTxO C.ConwayEra))
mkStartTx params wallet v b = do
  slotConfig <- asks pSlotConfig
  unspentOutputs <- E.utxosAt wallet
  uO <- E.utxosAtPlutus wallet

  let oref = fst (Map.foldrWithKey getLargest ((head (Map.keys uO)), (head (Map.elems uO))) uO)
      tin = toTxIn oref
      validInputs = C.unUTxO unspentOutputs
      validInput = [last (Map.keys validInputs)]
      debug = last (Map.elems validInputs)
      pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
  let utxos = Map.toList (C.unUTxO unspentOutputs)

  when (length (utxos) == 0) $
    throwError $
      E.CustomError $
        "no UTxOs"

  let utxo = head utxos
  let tn = "ThreadToken"
      an = "ThreadToken"
      cs = curSymbol params oref tn
      tt = assetClass cs tn

  let smAddress = mkAddress params
      txOut =
        C.TxOut
          smAddress
          (toTxOutValue (v <> assetClassValue tt 1))
          (toTxOutInlineDatum @Datum (tt, Holding))
          C.ReferenceScriptNone
      validityRange = toValidityRange slotConfig $ Interval.always
  let mintValue = threadTokenValue params oref tn an
      redeemer = V3.Redeemer (toBuiltinData ())

  let mintWitness =
        either (error . show) id $
          C.toCardanoMintWitness redeemer Nothing (Just (versionedPolicy params oref tn))

  let txMintValue =
        C.TxMintValue
          C.MaryEraOnwardsConway
          (mintValue)
          (C.BuildTxWith (Map.singleton (getPid params oref tn) mintWitness))

      witnessHeader =
        C.toCardanoTxInScriptWitnessHeader
          (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
      witness =
        C.BuildTxWith $
          C.KeyWitness C.KeyWitnessForSpending

      txIns = (,witness) <$> validInput

      extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh

  when (b) $
    throwError $
      E.CustomError $
        ( "Actually: "
            ++ show utxo
            ++ " and "
            ++ show uO
            ++ " and "
            ++ show extraKeyWit
            ++ " and "
            ++ show tin
            ++ " and "
            ++ show oref
        )
  let utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          , C.txMintValue = txMintValue
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsConway [extraKeyWit]
          }
      utxoIndex = unspentOutputs
   in pure (C.CardanoBuildTx utx, utxoIndex, oref, tin, debug)

start
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> Value
  -> Bool
  -> m (TxOutRef, C.TxIn, (C.TxOut C.CtxUTxO C.ConwayEra))
start wallet privateKey params v b = do
  E.logInfo @String $ "Starting"
  (utx, utxoIndex, oref, tin, tout) <- mkStartTx params wallet v b
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx
  return (oref, tin, tout)

mkProposeTx
  :: (E.MonadEmulator m)
  => Params
  -> Value
  -> PaymentPubKeyHash
  -> Integer
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkProposeTx params val pkh d tt = do
  let smAddress = mkAddress params
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

  when (length (validUnspentOutputs') == 0) $
    throwError $
      E.CustomError $
        ("found no SM but: " ++ (show unspentOutputs))
  when (length (validUnspentOutputs') > 1) $
    throwError $
      E.CustomError $
        "found too many SM"
  let
    remainingValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs')
    datum = (tt, (Collecting val (unPaymentPubKeyHash pkh) d []))
    remainingOutputs =
      [C.TxOut smAddress (toTxOutValue remainingValue) (toTxOutInlineDatum datum) C.ReferenceScriptNone]

    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Propose val (unPaymentPubKeyHash pkh) d)
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
  -> Integer
  -> AssetClass
  -> m TxSuccess
propose wallet privateKey params val pkh d tt = do
  E.logInfo @String "Proposing"
  (utx, utxoIndex) <- mkProposeTx params val pkh d tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

cardanoTxOutDatum :: forall d. (FromData d) => C.TxOut C.CtxUTxO C.ConwayEra -> Maybe d
cardanoTxOutDatum (C.TxOut _aie _tov tod _rs) =
  case tod of
    C.TxOutDatumNone ->
      Nothing
    C.TxOutDatumHash _era _scriptDataHash ->
      Nothing
    C.TxOutDatumInline _era scriptData ->
      fromData @d $ C.toPlutusData $ C.getScriptData scriptData

mkAddTx
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkAddTx params wallet tt = do
  let smAddress = mkAddress params
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
    datums = map (cardanoTxOutDatum @Datum) (Map.elems validUnspentOutputs)
    datum = case datums of
      (Just (tt, (Collecting v pkh' d sigs))) : _ ->
        (tt, (Collecting v pkh' d (insert (unPaymentPubKeyHash pkh) sigs)))
      otherwise -> (tt, Holding)
    remainingOutputs =
      [C.TxOut smAddress (toTxOutValue remainingValue) (toTxOutInlineDatum datum) C.ReferenceScriptNone]

    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Add (unPaymentPubKeyHash pkh))
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
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

add
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> AssetClass
  -> m TxSuccess
add wallet privateKey params tt = do
  E.logInfo @String "Adding"
  (utx, utxoIndex) <- mkAddTx params wallet tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

toPkhAddress :: PaymentPubKeyHash -> Ledger.CardanoAddress
toPkhAddress pkh =
  C.makeShelleyAddressInEra
    C.shelleyBasedEra
    testnet
    (either (error . show) C.PaymentCredentialByKey $ C.toCardanoPaymentKeyHash pkh)
    C.NoStakeAddress

mkPayTx
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkPayTx params wallet tt = do
  let smAddress = mkAddress params
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
    currentValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
    datums = map (cardanoTxOutDatum @Datum) (Map.elems validUnspentOutputs)
    (datum, (v, pkh2)) = case datums of
      (Just (tt, (Collecting v pkh' d sigs))) : _ ->
        ((tt, Holding), (v, pkh'))
      otherwise -> ((tt, Holding), (mempty, (unPaymentPubKeyHash pkh)))
    remainingOutputs =
      [ C.TxOut
          smAddress
          (toTxOutValue (currentValue <> (PlutusTx.negate v)))
          (toTxOutInlineDatum datum)
          C.ReferenceScriptNone
      , C.TxOut
          (toPkhAddress (Ledger.PaymentPubKeyHash{unPaymentPubKeyHash = pkh2}))
          (toTxOutValue v)
          C.TxOutDatumNone
          C.ReferenceScriptNone
      ]
    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Pay)
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
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

pay
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> AssetClass
  -> m TxSuccess
pay wallet privateKey params tt = do
  E.logInfo @String "Paying"
  (utx, utxoIndex) <- mkPayTx params wallet tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

mkCancelTx
  :: (E.MonadEmulator m)
  => Params
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkCancelTx params tt = do
  let smAddress = mkAddress params
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
    datums = map (cardanoTxOutDatum @Datum) (Map.elems validUnspentOutputs)
    (datum, d) = case datums of
      (Just (tt, (Collecting v pkh d' sigs))) : _ ->
        ((tt, Holding), d')
      otherwise -> ((tt, Holding), 0)

    remainingOutputs =
      [C.TxOut smAddress (toTxOutValue remainingValue) (toTxOutInlineDatum datum) C.ReferenceScriptNone]

    validityRange = toValidityRange slotConfig $ Interval.from (POSIXTime (d + 1000))
    redeemer = toHashableScriptData (Cancel)
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
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
        }
   in
    pure (C.CardanoBuildTx utx, unspentOutputs)

cancel
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> AssetClass
  -> m TxSuccess
cancel wallet privateKey params tt = do
  E.logInfo @String "Cancelling"
  (utx, utxoIndex) <- mkCancelTx params tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

mkStopTx
  :: (E.MonadEmulator m)
  => Params
  -> AssetClass
  -> C.TxIn
  -> Bool
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkStopTx params tt tin b = do
  let smAddress = mkAddress params
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

  when (b) $
    throwError $
      E.CustomError $
        ("Actually: " ++ show (currentValue) ++ " and " ++ show validUnspentOutputs)
  let
    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Stop)
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
    witness =
      C.BuildTxWith $
        C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
    txIns = (,witness) <$> Map.keys validUnspentOutputs

  let
    tn = "ThreadToken"
    an = "ThreadToken"
    oref = C.fromCardanoTxIn tin
    mintValue = burnTokenValue params oref tn an
    mintWitness =
      either (error . show) id $
        C.toCardanoMintWitness
          (V3.Redeemer (toBuiltinData ()))
          Nothing
          (Just (versionedPolicy params oref tn))
    txMintValue =
      C.TxMintValue
        C.MaryEraOnwardsConway
        (mintValue)
        (C.BuildTxWith (Map.singleton (getPid params oref tn) mintWitness))
    utx =
      E.emptyTxBodyContent
        { C.txIns = txIns
        , C.txMintValue = txMintValue
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        }
   in
    pure (C.CardanoBuildTx utx, unspentOutputs)

stop
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> AssetClass
  -> C.TxIn
  -> Bool
  -> m TxSuccess
stop wallet privateKey params tt tin b = do
  E.logInfo @String "Stopping"
  (utx, utxoIndex) <- mkStopTx params tt tin b
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx
