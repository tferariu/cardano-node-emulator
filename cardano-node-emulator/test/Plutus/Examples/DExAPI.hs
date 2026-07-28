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

-- | Off-chain code for the Limit Order Book Distributed Exchange contract
module Plutus.Examples.DExAPI (
  -- * Actions
  update,
  exchange,
  start,
  stop,
  getPayAmt,
  paymentValue,
  unite,
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
import Plutus.Examples.DEx
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
import PlutusLedgerApi.V3 hiding (Datum, Redeemer, TxId, ratio)
import PlutusLedgerApi.V3 qualified as V3
import PlutusLedgerApi.V3.Contexts hiding (TxId)
import PlutusTx qualified
import PlutusTx.Code (getCovIdx)
import PlutusTx.Coverage (CoverageIndex)
import PlutusTx.Prelude (traceError, traceIfFalse)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Ratio hiding (ratio)

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

someTokenValue :: AssetClass -> Integer -> C.Value
someTokenValue ac i = C.valueFromList [(toAssetId ac, C.Quantity i)]

lovelaces :: Value -> Integer
lovelaces v = assetClassValueOf v (AssetClass (adaSymbol, adaToken))

getPayAmt :: Integer -> PlutusLedgerApi.V3.Rational -> Integer
getPayAmt amt r =
  if mod (amt * numerator r) (denominator r) == 0
    then div (amt * numerator r) (denominator r)
    else (div (amt * numerator r) (denominator r)) + 1

paymentValue :: CurrencySymbol -> TokenName -> Integer -> Value
paymentValue cs tn amt = singleton cs tn amt

cardanoTxOutDatum :: forall d. (FromData d) => C.TxOut C.CtxUTxO C.ConwayEra -> Maybe d
cardanoTxOutDatum (C.TxOut _aie _tov tod _rs) =
  case tod of
    C.TxOutDatumNone ->
      Nothing
    C.TxOutDatumHash _era _scriptDataHash ->
      Nothing
    C.TxOutDatumInline _era scriptData ->
      fromData @d $ C.toPlutusData $ C.getScriptData scriptData

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

toPkhAddress :: PaymentPubKeyHash -> Ledger.CardanoAddress
toPkhAddress pkh =
  C.makeShelleyAddressInEra
    C.shelleyBasedEra
    testnet
    (either (error . show) C.PaymentCredentialByKey $ C.toCardanoPaymentKeyHash pkh)
    C.NoStakeAddress

newtype TxSuccess = TxSuccess TxId
  deriving (Eq, Show)

-- traceShowM $ debug -- for debugging

------------------------------------------------------------------------------------------------------------------------------
-- Building and submitting the transactions
------------------------------------------------------------------------------------------------------------------------------

mkStartTx
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> Value
  -> PlutusLedgerApi.V3.Rational
  -> Bool
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex, TxOutRef, C.TxIn, (C.TxOut C.CtxUTxO C.ConwayEra))
mkStartTx params wallet v r b = do
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
          (toTxOutInlineDatum @Datum (tt, (Label r (unPaymentPubKeyHash pkh))))
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
  -> PlutusLedgerApi.V3.Rational
  -> Bool
  -> m (TxOutRef, C.TxIn, (C.TxOut C.CtxUTxO C.ConwayEra))
start wallet privateKey params v r b = do
  E.logInfo @String $ "Starting"
  (utx, utxoIndex, oref, tin, tout) <- mkStartTx params wallet v r b
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx
  return (oref, tin, tout)

mkUpdateTx
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> Value
  -> PlutusLedgerApi.V3.Rational
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkUpdateTx params wallet v r tt = do
  let smAddress = mkAddress params
      pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  uO <- E.utxosAtPlutus wallet
  wUtxo <- (E.utxosAt wallet)
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
    validW =
      Map.filter
        (\(C.TxOut _aie tov _tod _rs) -> True)
        $ Map.fromList [last (Map.toList (C.unUTxO wUtxo))]

  when (length (validUnspentOutputs) == 0) $
    throwError $
      E.CustomError $
        ("found no SM but: " ++ (show unspentOutputs))

  when (length (validUnspentOutputs) /= 1) $
    throwError $
      E.CustomError $
        "not SM"
  let
    currentValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
    remainingValue = v
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
    datums = map (cardanoTxOutDatum @Datum) (Map.elems validUnspentOutputs)
    datum = case datums of
      (Just (tt', i)) : _ -> (tt', (Label r (owner i)))
      otherwise -> (tt, (Label r (unPaymentPubKeyHash pkh)))

    remainingOutputs =
      [C.TxOut smAddress (toTxOutValue remainingValue) (toTxOutInlineDatum datum) C.ReferenceScriptNone]

    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Update v r)
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
    witness =
      C.BuildTxWith $
        C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits

  let
    newTxIns =
      map (,C.BuildTxWith $ C.KeyWitness C.KeyWitnessForSpending) $
        Map.keys $
          Map.fromList [last (Map.toList (C.unUTxO wUtxo))]

    txIns = ((,witness) <$> Map.keys validUnspentOutputs) -- ++ newTxIns
    oref = fst (Map.foldrWithKey getLargest ((head (Map.keys uO)), (head (Map.elems uO))) uO)
    tin = toTxIn oref

  let
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

update
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Value
  -> PlutusLedgerApi.V3.Rational
  -> Ledger.PaymentPrivateKey
  -> Params
  -> AssetClass
  -> m TxSuccess
update wallet v r privateKey params tt = do
  E.logInfo @String "Updating"
  (utx, utxoIndex) <- mkUpdateTx params wallet v r tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

mkExchangeTx
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> Integer
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkExchangeTx params wallet amt tt = do
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
    (tt', i) = case datums of
      (Just (tt', i)) : _ -> (tt', i)
      otherwise -> error "impossible"
    v =
      paymentValue
        (fst (unAssetClass (buyCurr params)))
        (snd (unAssetClass (buyCurr params)))
        (getPayAmt amt (ratio i))
    buy =
      paymentValue
        (fst (unAssetClass (sellCurr params)))
        (snd (unAssetClass (sellCurr params)))
        amt
    remainingOutputs =
      [ C.TxOut
          smAddress
          (toTxOutValue (currentValue <> (PlutusTx.negate buy)))
          (toTxOutInlineDatum (tt', i))
          C.ReferenceScriptNone
      , C.TxOut
          (toPkhAddress (Ledger.PaymentPubKeyHash (owner i)))
          (toTxOutValue (v <> minValue))
          C.TxOutDatumNone
          C.ReferenceScriptNone
      ]
    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Exchange amt (unPaymentPubKeyHash pkh))
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
    witness =
      C.BuildTxWith $
        C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
    txIns = (,witness) <$> Map.keys validUnspentOutputs

  let
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

exchange
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Integer
  -> Ledger.PaymentPrivateKey
  -> Params
  -> AssetClass
  -> m TxSuccess
exchange wallet amt privateKey params tt = do
  E.logInfo @String "Exchanging"
  (utx, utxoIndex) <- mkExchangeTx params wallet amt tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

mkStopTx
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> AssetClass
  -> C.TxIn
  -> Bool
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkStopTx params wallet tt tin b = do
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
    pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
    tn = "ThreadToken"
    an = "ThreadToken"
    oref = C.fromCardanoTxIn tin
    mintValue = burnTokenValue' tt
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
  let
    utx =
      E.emptyTxBodyContent
        { C.txIns = txIns
        , C.txMintValue = txMintValue
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsConway [extraKeyWit]
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
  (utx, utxoIndex) <- mkStopTx params wallet tt tin b
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

{-
Submitting a transaction to consolidate wallet outputs, otherwise there are issues with
selecting which UTxO to spend. Does not actually use the smart contract at all
-}
mkUniteTx
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkUniteTx wallet = do
  let pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange

  uO <- E.utxosAtPlutus wallet
  wUtxo <- (E.utxosAt wallet)
  let
    validW =
      Map.filter
        (\(C.TxOut _aie tov _tod _rs) -> True)
        $ Map.fromList [last (Map.toList (C.unUTxO wUtxo))]
    values =
      map
        (\(C.TxOut _aie tov _tod _rs) -> C.fromCardanoValue (C.fromCardanoTxOutValue tov))
        (Map.elems (C.unUTxO wUtxo))
    val = (foldl (<>) emptyValue values) <> (PlutusTx.negate minValue)

  let
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh

    remainingOutputs =
      [ C.TxOut
          (toPkhAddress pkh)
          (toTxOutValue val)
          C.TxOutDatumNone
          C.ReferenceScriptNone
      ]

    validityRange = toValidityRange slotConfig $ Interval.from current

  let
    utx =
      E.emptyTxBodyContent
        { C.txOuts = remainingOutputs
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsConway [extraKeyWit]
        }
   in
    pure (C.CardanoBuildTx utx, wUtxo)

unite
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> m TxSuccess
unite wallet privateKey = do
  E.logInfo @String "Uniting"
  (utx, utxoIndex) <- mkUniteTx wallet
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx
