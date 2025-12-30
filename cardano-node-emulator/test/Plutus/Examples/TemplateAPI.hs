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

-- | Off-chain code for the Account Simulation contract
module Plutus.Examples.TemplateAPI (
  -- * Actions
  start,
  doSomething,
  close,
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
import Plutus.Examples.Template
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
import PlutusLedgerApi.V1.Value qualified as V
import PlutusLedgerApi.V2.Tx hiding (TxId)
import PlutusLedgerApi.V3 hiding (TxId)
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
-- Creating the transaction that puts the contract on the blockchain
------------------------------------------------------------------------------------------------------------------------------

mkStartTx
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex, TxOutRef, C.TxIn)
mkStartTx par wallet = do
  slotConfig <- asks pSlotConfig
  -- get the unspent outputs of the wallet submitting the transaction
  uO <- E.utxosAtPlutus wallet

  -- get the output reference and TxIn for the UTxO being spent from the wallet
  -- we take the largest so that we have enough ada to pay for fees/collateral
  let oref = fst (Map.foldrWithKey getLargest ((head (Map.keys uO)), (head (Map.elems uO))) uO)
      tin = toTxIn oref

  -- throw an error if there are no utxos to be spent
  when (length (uO) == 0) $
    throwError $
      E.CustomError $
        "no UTxOs"

  -- create the Thread Token
  let tn = "ThreadToken"
      an = "ThreadToken"
      cs = curSymbol par oref tn
      tt = assetClass cs tn

  -- make the smart contract output
  let smAddress = mkAddress par
      txOut =
        C.TxOut
          smAddress
          (toTxOutValue (minValue <> assetClassValue tt 1 <> x2MinValue))
          (toTxOutInlineDatum @Label (tt, 0))
          C.ReferenceScriptNone

  -- other transaction components
  let validityRange = toValidityRange slotConfig $ Interval.always
      redeemer = Redeemer (toBuiltinData ())

  -- mint the token
  let mintValue = threadTokenValue par oref tn an
      mintWitness =
        either (error . show) id $
          C.toCardanoMintWitness redeemer Nothing (Just (versionedPolicy par oref tn))
      txMintValue =
        C.TxMintValue
          C.MaryEraOnwardsConway
          (mintValue)
          (C.BuildTxWith (Map.singleton (getPid par oref tn) mintWitness))

  -- make the transaction body
  let utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          , C.txMintValue = txMintValue
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          }
      utxoIndex = mempty
   in pure (C.CardanoBuildTx utx, utxoIndex, oref, tin)

--  Submitting the transaction
start
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> m (TxOutRef, C.TxIn)
start wallet privateKey par = do
  E.logInfo @String $ "Starting"
  (utx, utxoIndex, oref, tin) <- mkStartTx par wallet
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx
  return (oref, tin)

------------------------------------------------------------------------------------------------------------------------------
-- Creating the transaction that does something, in this case move some value from the contract
------------------------------------------------------------------------------------------------------------------------------

mkSomethingTx
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> Value
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkSomethingTx par wallet val tt = do
  let smAddress = mkAddress par
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

  when (length (validUnspentOutputs) /= 1) $
    throwError $
      E.CustomError $
        "not SM"

  let
    remainingValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
    datums = map (cardanoTxOutDatum @Label) (Map.elems validUnspentOutputs)
    datum = case datums of
      (Just (tt', label)) : _ -> (tt', label)
      otherwise -> (tt, 0)
    -- since this transaction is not just internal we need to adjust the value
    remainingOutputs =
      [ C.TxOut
          smAddress
          (toTxOutValue (remainingValue <> (PlutusTx.negate val)))
          (toTxOutInlineDatum datum)
          C.ReferenceScriptNone
      ]
    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Placeholder')
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator par))
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

-- Submitting the transaction
doSomething
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> Value
  -> AssetClass
  -> m TxSuccess
doSomething wallet privateKey par val tt = do
  E.logInfo @String "Doing Something"
  (utx, utxoIndex) <- mkSomethingTx par wallet val tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

------------------------------------------------------------------------------------------------------------------------------
-- Creating the transaction that removes the contract from the blockchain and burns the thread token
------------------------------------------------------------------------------------------------------------------------------

mkCloseTx
  :: (E.MonadEmulator m)
  => Params
  -> AssetClass
  -> C.TxIn
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkCloseTx par tt tin = do
  let smAddress = mkAddress par
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
    redeemer = toHashableScriptData (Placeholder')
    witnessHeader =
      C.toCardanoTxInScriptWitnessHeader
        (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator par))
    witness =
      C.BuildTxWith $
        C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
    txIns = (,witness) <$> Map.keys validUnspentOutputs

  -- spend the contract without perpetuating it and burn the thread token
  let
    tn = "ThreadToken"
    an = "ThreadToken"
    oref = C.fromCardanoTxIn tin
    mintValue = burnTokenValue par oref tn an
    mintWitness =
      either (error . show) id $
        C.toCardanoMintWitness (Redeemer (toBuiltinData ())) Nothing (Just (versionedPolicy par oref tn))
    txMintValue =
      C.TxMintValue
        C.MaryEraOnwardsConway
        (mintValue)
        (C.BuildTxWith (Map.singleton (getPid par oref tn) mintWitness))
    utx =
      E.emptyTxBodyContent
        { C.txIns = txIns
        , C.txMintValue = txMintValue
        , C.txValidityLowerBound = fst validityRange
        , C.txValidityUpperBound = snd validityRange
        }
   in
    pure (C.CardanoBuildTx utx, unspentOutputs)

-- Submitting the Close transaction
close
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> AssetClass
  -> C.TxIn
  -> m TxSuccess
close wallet privateKey par tt tin = do
  E.logInfo @String "Closing"
  (utx, utxoIndex) <- mkCloseTx par tt tin
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx
