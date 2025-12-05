{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
-- maybe here the version stuff happens
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- {-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}

module Plutus.Examples.MultiSigSpec (
  tests,
  prop_MultiSig,
  prop_Check,
  checkPropMultiSigWithCoverage,
  {-prop_Escrow_DoubleSatisfaction,
  prop_FinishEscrow,
  prop_observeEscrow,
  prop_NoLockedFunds,
  prop_validityChecks,
  checkPropEscrowWithCoverage,
  EscrowModel,
  normalCertification,
  normalCertification',
  quickCertificationWithCheckOptions,
  outputCoverageOfQuickCertification,
  runS-}
) where

import Control.Lens (At (at), makeLenses, to, (%=), (.=), (^.))
import Control.Monad (void, when)
import Control.Monad.Trans (lift)
import Data.Default (Default (def))
import Data.Foldable (Foldable (fold, length, null), sequence_)
import Data.Map (Map)
import Data.Map qualified as Map
import GHC.Generics (Generic)

import Cardano.Api.Shelley (toPlutusData)
import Cardano.Node.Emulator qualified as E
import Cardano.Node.Emulator.Internal.Node.Params qualified as Params
import Cardano.Node.Emulator.Internal.Node.TimeSlot qualified as TimeSlot
import Cardano.Node.Emulator.Test (
  checkPredicateOptions,
  hasValidatedTransactionCountOfTotal,
  walletFundsChange,
  (.&&.),
 )
import Cardano.Node.Emulator.Test.Coverage (writeCoverageReport)
import Cardano.Node.Emulator.Test.NoLockedFunds (
  NoLockedFundsProof (nlfpMainStrategy, nlfpWalletStrategy),
  checkNoLockedFundsProofWithOptions,
  defaultNLFP,
 )
import Ledger (
  POSIXTime,
  PaymentPubKeyHash (unPaymentPubKeyHash),
  Slot,
  TxId,
  getCardanoTxId,
  minAdaTxOutEstimated,
 )
import Ledger qualified
import Ledger.Tx.CardanoAPI (fromCardanoSlotNo)
import Ledger.Typed.Scripts qualified as Scripts
import Ledger.Value.CardanoAPI qualified as Value
import Plutus.Script.Utils.Ada qualified as Ada
import Plutus.Script.Utils.Value (
  AssetClass (..),
  CurrencySymbol (..),
  TokenName (..),
  Value,
  assetClass,
  assetClassValue,
  geq,
  gt,
  valueOf,
 )
import PlutusLedgerApi.V1.Time (POSIXTime)

import Plutus.Examples.MultiSig hiding (Info (..), Input (..))

-- Params (..),

-- typedValidator,

import Plutus.Examples.MultiSig qualified as Impl
import Plutus.Examples.MultiSigAPI (
  add,
  cancel,
  close,
  pay,
  propose,
  start,
 )

import PlutusTx (fromData)
import PlutusTx.Monoid (inv)
import PlutusTx.Prelude qualified as PlutusTx

import Data.Maybe (fromJust)

import Cardano.Api (
  AddressInEra (AddressInEra),
  AllegraEraOnwards (AllegraEraOnwardsConway),
  AssetName (..),
  IsShelleyBasedEra (shelleyBasedEra),
  PolicyId (..),
  TxOut (TxOut),
  TxValidityLowerBound (TxValidityLowerBound, TxValidityNoLowerBound),
  TxValidityUpperBound (TxValidityUpperBound),
  UTxO (unUTxO),
  toAddressAny,
 )
import Test.QuickCheck qualified as QC hiding ((.&&.))
import Test.QuickCheck.ContractModel (
  Action,
  Actions,
  ContractModel,
  DL,
  RunModel,
  action,
  anyActions_,
  assertModel,
  contractState,
  currentSlot,
  deposit,
  forAllDL,
  lockedValue,
  observe,
  symIsZero,
  utxo,
  viewContractState,
  viewModelState,
  wait,
  waitUntilDL,
  withdraw,
 )
import Test.QuickCheck.ContractModel qualified as QCCM
import Test.QuickCheck.ContractModel.ThreatModel (
  IsInputOrOutput (addressOf),
  ThreatModel,
  anyInputSuchThat,
  changeValidityRange,
  getRedeemer,
  shouldNotValidate,
 )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (
  Property,
  choose,
  chooseInteger,
  frequency,
  testProperty,
 )

import Cardano.Api qualified as API
import PlutusTx.Builtins qualified as Builtins

import Debug.Trace

{-
curr2 :: CurrencySymbol
curr2 = "c7c9864fcc779b5573d97e3beefe5dd3705bbfe41972acd9bb6ebe9e"

on :: TokenName
on = "OtherToken"

ot :: AssetClass
ot = assetClass curr2 tn
-}
type Wallet = Integer

w1, w2, w3, w4, w5, w6 :: Wallet
w1 = 1
w2 = 2
w3 = 3
w4 = 4
w5 = 5
w6 = 6

walletAddress :: Wallet -> Ledger.CardanoAddress
walletAddress = (E.knownAddresses !!) . pred . fromIntegral

walletPrivateKey :: Wallet -> Ledger.PaymentPrivateKey
walletPrivateKey = (E.knownPaymentPrivateKeys !!) . pred . fromIntegral

testWallets :: [Wallet]
testWallets = [w1, w2, w3, w4, w5, w6] -- removed five to increase collisions (, w6, w7, w8, w9, w10])

walletPaymentPubKeyHash :: Wallet -> Ledger.PaymentPubKeyHash
walletPaymentPubKeyHash =
  Ledger.PaymentPubKeyHash
    . Ledger.pubKeyHash
    . Ledger.unPaymentPubKey
    . (E.knownPaymentPublicKeys !!)
    . pred
    . fromIntegral

modelParams :: Params
modelParams =
  Params
    { authSigs =
        [ unPaymentPubKeyHash (walletPaymentPubKeyHash w4)
        , unPaymentPubKeyHash (walletPaymentPubKeyHash w5)
        , unPaymentPubKeyHash (walletPaymentPubKeyHash w3)
        ]
    , nr = 2
    , maxWait = 2000000000
    }

tn :: TokenName
tn = "ThreadToken"

curr :: CurrencySymbol
curr = "16bb488ea35b8741fe56f5c1abea2caa32a2a2ff0e8a695b34bb2caf"

tn' :: TokenName
tn' = "ThreadToken"

curr' :: CurrencySymbol
curr' = "5e30874bfcf9c89a5378d6bedccb3c7592b1e5b16c959be06c251cec" -- "fdcfa80f3cd89b403225688ce8c8c7ee2437a4bf137f481abbc7263b"

tn'' :: TokenName
tn'' = "ThreadToken"

curr'' :: CurrencySymbol
curr'' = "302ab3c023d2d3a2ca0fd2d25b8ca68725bd05b4f88cbde01cade0a1"

tin :: API.TxIn
tin = API.TxIn "b0de2873afe95a6530bf1ae88096cf43e17bb2ee669f9ba600838949ac1e08ec" (API.TxIx 5)

tin' :: API.TxIn
tin' = API.TxIn "a8bbf3c00719fca852c087aa7c2cae9023cb0f66d8492536fcbddeb2007ae7a0" (API.TxIx 1)

-- API.TxIn "9b46c94581afc2e1e81e9cacfd0cf734b6b8512bade903cd88e9b59b5e192045" (API.TxIx 1)

tin'' :: API.TxIn
tin'' = API.TxIn "b0de2873afe95a6530bf1ae88096cf43e17bb2ee669f9ba600838949ac1e08ec" (API.TxIx 4)

ok :: Bool
ok = False

ok' :: Bool
ok' = False

-- "ebccd1c5c11830d79458ff798e3ce918020dae161cb1ba377637b81e"

-- curSymbol modelParams oref?? tn
{-
UTxO {unUTxO = fromList [(TxIn \"bf0f8addee8b501dcbeb4ef0309e41ea765a3613d50dd854a852408407c32111\" (TxIx 0),
TxOut (AddressInEra (ShelleyAddressInEra ShelleyBasedEraConway) (ShelleyAddress Testnet (ScriptHashObj
(ScriptHash \"1abefe14b0d3052a84f54276f3efac6f0345eb4a0b14dc271480eabc\")) StakeRefNull))
(TxOutValueShelleyBased ShelleyBasedEraConway (MaryValue (Coin 100000000)
(MultiAsset (fromList [(PolicyID {policyID = ScriptHash \"e53087fb4c98a17c2b71562ee5ba6cf57c1d9fd01157fe3721d20330\"},
fromList [(\"546872656164546f6b656e\",1)])])))) (TxOutDatumInline BabbageEraOnwardsConway
(HashableScriptData \"\\216y\\159\\216y\\128\\216y\\159X\\FS\\229\\&0\\135\\251L\\152\\161|+qV.\\229\\186l\\245|\\GS\\159\\208\\DC1W\\254\
\&7!\\210\\ETX0KThreadToken\\255\\255\" (ScriptDataConstructor 0 [ScriptDataConstructor 0 [],ScriptDataConstructor 0
[ScriptDataBytes \"\\229\\&0\\135\\251L\\152\\161|+qV.\\229\\186l\\245|\\GS\\159\\208\\DC1W\\254\\&7!\\210\\ETX0\",ScriptDataBytes \"ThreadToken\"]])))
ReferenceScriptNone)]}"
-}

tt :: AssetClass
tt = assetClass curr tn

tt' :: AssetClass
tt' = assetClass curr' tn'

makeTT :: Ledger.TxOutRef -> AssetClass
makeTT oref = assetClass (curSymbol modelParams oref tn) tn

data Phase
  = Initial
  | Holding
  | Collecting
  deriving (Show, Eq, Generic)

data MultiSigModel = MultiSigModel
  { _actualValue :: Value
  , _allowedSignatories :: [Wallet]
  , _requiredSignatories :: Integer
  , _threadToken :: Maybe QCCM.SymToken -- AssetClass
  , _txIn :: Maybe QCCM.SymTxIn
  , _phase :: Phase
  , _paymentValue :: Value
  , _paymentTarget :: Maybe Wallet
  , _deadline :: Maybe Integer
  , _actualSignatories :: [Wallet]
  }
  deriving (Eq, Show, Generic)

makeLenses ''MultiSigModel

options :: E.Options MultiSigModel
options =
  E.defaultOptions
    { E.initialDistribution = defInitialDist
    , E.params = Params.increaseTransactionLimits def
    , E.coverageIndex = Impl.covIdx
    }

genWallet :: QC.Gen Wallet
genWallet = QC.elements testWallets

genTT :: QC.Gen AssetClass
genTT = QC.elements [tt]

beginningOfTime :: Integer
beginningOfTime = 1596059091000

instance ContractModel MultiSigModel where
  data Action MultiSigModel
    = Propose Wallet Value Wallet Integer
    | Add Wallet
    | Pay Wallet
    | Cancel Wallet
    | Start Wallet Value
    | Close Wallet
    deriving (Eq, Show, Generic)

  initialState =
    MultiSigModel
      { _actualValue = mempty
      , _allowedSignatories = [w5, w3, w4]
      , _requiredSignatories = (nr modelParams)
      , _threadToken = Nothing -- tt --AssetClass (adaSymbol, adaToken)
      , _phase = Initial
      , _paymentValue = mempty
      , _paymentTarget = Nothing
      , _deadline = Nothing
      , _actualSignatories = []
      , _txIn = Nothing
      }

  -- here?
  nextState a = void $ case a of
    Propose w1 v w2 d -> do
      phase .= Collecting
      paymentValue .= v
      paymentTarget .= Just w2
      --      curSlot <- viewModelState currentSlot
      --      endSlot .= curSlot + deadline
      deadline .= Just d
      wait 1
    Add w -> do
      actualSignatories' <- viewContractState actualSignatories
      actualSignatories
        %= ( case (elem w actualSignatories') of -- (w:)
              True -> id
              False -> (w :)
           )
      wait 1
    {-
    actualSignatories' <- viewContractState actualSignatories
    actualSignatories’ = nub (w : actualSignatories)
    -}
    Pay w -> do
      phase .= Holding
      deadline .= Nothing
      address <- viewContractState paymentTarget
      paymentTarget .= Nothing
      actualSignatories .= []
      actualValue' <- viewContractState actualValue
      paymentValue' <- viewContractState paymentValue
      actualValue .= actualValue' <> (PlutusTx.negate paymentValue')
      deposit (walletAddress (fromJust address)) paymentValue'
      paymentValue .= mempty
      wait 1
    Cancel w -> do
      phase .= Holding
      actualSignatories .= []
      paymentTarget .= Nothing
      paymentValue .= mempty
      deadline .= Nothing
      wait 1
    Start w v -> do
      phase .= Holding
      withdraw (walletAddress w) (v) -- <> (assetClassValue tt 1))
      actualValue .= v
      symToken <- QCCM.createToken "thread token"
      threadToken .= Just symToken
      symTxIn <- QCCM.createTxIn "minting input"
      txIn .= Just symTxIn
      actualSignatories .= []
      wait 1
    Close w -> do
      phase .= Initial
      actualValue' <- viewContractState actualValue
      deposit (walletAddress w) (actualValue') -- <> (fromJust (viewContractState threadToken)))
      actualValue .= mempty
      threadToken .= Nothing
      actualSignatories .= []
      wait 1

  -- (fromJust (translate <$> s ^. contractState . threadToken))

  precondition s a = case a of
    Propose w1 v w2 d -> currentPhase == Holding && (currentValue `geq` v) && (v `geq` minValue)
    Add w -> currentPhase == Collecting && (elem w sigs) -- && not (elem w actualSigs)
    Pay w -> currentPhase == Collecting && ((length actualSigs) >= (fromIntegral min)) && w == receiver
    Cancel w -> currentPhase == Collecting && ((d + 2000) < timeInt)
    Start w v -> currentPhase == Initial && (v `geq` x2MinValue)
    Close w -> currentPhase == Holding && ((Ada.toValue Ledger.minAdaTxOutEstimated) `gt` currentValue)
    where
      currentPhase = s ^. contractState . phase
      currentValue = (s ^. contractState . actualValue) <> (PlutusTx.negate (Ada.toValue 3000000)) -- liquid value
      sigs = s ^. contractState . allowedSignatories
      actualSigs = s ^. contractState . actualSignatories
      min = s ^. contractState . requiredSignatories
      slot = s ^. currentSlot . to fromCardanoSlotNo
      time = TimeSlot.slotToBeginPOSIXTime def slot
      timeInt = Ledger.getPOSIXTime time
      d = fromJust $ (s ^. contractState . deadline)
      receiver = fromJust $ (s ^. contractState . paymentTarget)

  {-
      Redeem _ ->
        (s ^. contractState . contributions . to Data.Foldable.fold)
          `geq` (s ^. contractState . targets . to Data.Foldable.fold)
          && ( s ^. currentSlot . to fromCardanoSlotNo
                < s ^. contractState . refundSlot - 2
             )
      Refund w ->
        s ^. currentSlot . to fromCardanoSlotNo
          > s ^. contractState . refundSlot
          && Nothing /= (s ^. contractState . contributions . at w)
      Pay _ v ->
        s ^. currentSlot . to fromCardanoSlotNo
          < s ^. contractState . refundSlot - 2
          && Ada.adaValueOf (fromInteger v) `geq` Ada.toValue Ledger.minAdaTxOutEstimated
      BadRefund w w' ->
        s ^. currentSlot . to fromCardanoSlotNo < s ^. contractState . refundSlot - 2 -- why -2?
          || w /= w'-}

  -- enable again later
  validFailingAction _ _ = False

  -- put token back in Start
  arbitraryAction s =
    frequency
      [
        ( 2
        , Propose
            <$> genWallet
            <*> ( Ada.lovelaceValueOf
                    <$> choose ((Ada.getLovelace Ledger.minAdaTxOutEstimated), valueOf amount Ada.adaSymbol Ada.adaToken)
                )
            <*> genWallet
            <*> chooseInteger (timeInt, timeInt + 10000)
        )
      , (10, Add <$> genWallet)
      , (10, Pay <$> genWallet)
      , (1, Cancel <$> genWallet)
      ,
        ( 1
        , Start
            <$> genWallet
            <*> ( Ada.lovelaceValueOf
                    <$> choose (((Ada.getLovelace Ledger.minAdaTxOutEstimated) * 2), 100_000_000)
                )
        )
      , (3, Close <$> genWallet)
      ]
    where
      amount = (s ^. contractState . actualValue) -- <> (PlutusTx.negate (Ada.toValue Ledger.minAdaTxOutEstimated))
      slot = s ^. currentSlot . to fromCardanoSlotNo
      time = TimeSlot.slotToEndPOSIXTime def slot
      timeInt = Ledger.getPOSIXTime time

-- int' = Ledger.getSlot slot'

{-instance RunModel MultiSigModel E.EmulatorM where
  perform _ cmd _ = lift $ void $ act cmd-}

act' :: Action MultiSigModel -> AssetClass -> E.EmulatorM ()
act' a tok = case a of
  Propose w1 v w2 d ->
    void $
      propose
        (walletAddress w1)
        (walletPrivateKey w1)
        modelParams
        v
        (walletPaymentPubKeyHash w2)
        d
        tok
  Add w ->
    void $
      add
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tok
  Pay w ->
    void $
      pay
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tok
  Cancel w ->
    void $
      cancel
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tok
  Start w v ->
    void $
      start
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        v
        ok
  Close w ->
    void $
      close
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tok
        tin'
        ok'

act :: Action MultiSigModel -> E.EmulatorM ()
act = \case
  Propose w1 v w2 d ->
    void $
      propose
        (walletAddress w1)
        (walletPrivateKey w1)
        modelParams
        v
        (walletPaymentPubKeyHash w2)
        d
        tt
  Add w ->
    void $
      add
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tt
  Pay w ->
    void $
      pay
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tt
  Cancel w ->
    void $
      cancel
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tt
  Start w v ->
    void $
      start
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        v
        False
  Close w ->
    void $
      close
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tt
        tin
        False

toAssetId :: AssetClass -> API.AssetId
toAssetId (AssetClass (sym, tok))
  | sym == Ada.adaSymbol, tok == Ada.adaToken = API.AdaAssetId
  | otherwise = API.AssetId (toPolicyId sym) (toAssetName tok)

toPolicyId :: CurrencySymbol -> API.PolicyId
toPolicyId sym@(CurrencySymbol bs) =
  either
    (error . show)
    API.PolicyId
    (API.deserialiseFromRawBytes API.AsScriptHash (Builtins.fromBuiltin bs))

{-
  | Just hash <- API.deserialiseFromRawBytes API.AsScriptHash
                                                    (Builtins.fromBuiltin bs) = API.PolicyId hash
  | otherwise = error $ "Bad policy id: " ++ show sym-}

toAssetName :: TokenName -> API.AssetName
toAssetName (TokenName bs) = API.AssetName $ Builtins.fromBuiltin bs

fromAssetId :: API.AssetId -> AssetClass
fromAssetId API.AdaAssetId = AssetClass (Ada.adaSymbol, Ada.adaToken)
fromAssetId (API.AssetId policy name) = AssetClass (fromPolicyId policy, fromAssetName name)

fromPolicyId :: API.PolicyId -> CurrencySymbol
fromPolicyId (API.PolicyId hash) = CurrencySymbol . Builtins.toBuiltin $ API.serialiseToRawBytes hash

fromAssetName :: API.AssetName -> TokenName
fromAssetName (API.AssetName bs) = TokenName $ Builtins.toBuiltin bs

{-
registerTxOutRef :: Monad m => String -> Ledger.TxOutRef -> QCCM.RunMonad m ()
registerTxOutRef = QCCM.registerSymbolic
-}

{-QCCM.registerToken "thread token" (toAssetId (makeTT oref))

  {-QCCM.registerToken "thread token" (toAssetId (makeTT oref))
  --QCCM.registerToken "thread token" (toAssetId (makeTT oref))
  --QCCM.registerTxIn "minting input" tin
  {-
  QCCM.registerToken "thread token" (toAssetId (makeTT oref)) -}-}-}

instance RunModel MultiSigModel E.EmulatorM where
  --  perform _ cmd _ = lift $ act cmd

  perform s (Start w v) translate = do
    (oref, tin, tout) <- lift $ start (walletAddress w) (walletPrivateKey w) modelParams v False
    QCCM.registerToken "thread token" (toAssetId (makeTT oref))
    QCCM.registerTxIn "minting input" (tin)
  perform s (Propose w1 v w2 d) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      propose
        (walletAddress w1)
        (walletPrivateKey w1)
        modelParams
        v
        (walletPaymentPubKeyHash w2)
        d
        ttref
  perform s (Add w) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      add
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        ttref
  perform s (Pay w) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      pay
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        ttref
  perform s (Cancel w) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      cancel
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        ttref
  perform s (Close w) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
        tinref = fromJust (translate <$> s ^. contractState . txIn)
    lift $
      close
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        ttref
        tinref
        False

{-
  void $ do
    let mref = translate <$> s ^. contractState . txIn
        lotto = s ^. contractState . value
        sealPolicy = TScripts.Versioned (Lib.mkMintingPolicy Lotto.script) TScripts.PlutusV2
        currency = L.scriptCurrencySymbol sealPolicy
    (ref, txout, tname) <- Lotto.mintSeal (Plutus.fromCardanoTxIn $ fromJust mref)
                                          (Ada.adaValueOf $ fromInteger lotto)
    registerTxIn "Lotto txIn"  (toTxIn ref)
    registerToken "threadToken" (toAssetId (assetClass currency tname))

  Start w v tt ->
      start
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        v

perform _ Offer _ = void $ do
    ref <- Auction.txOffer (wallet 1) (banana 1) 30_000_000
    registerTxIn "auction txIn" (toTxIn ref)
  perform s Hammer translate = void $ do
    let mref = translate <$> s ^. contractState . txIn
    Auction.txHammer (wallet 1) (Plutus.fromCardanoTxIn $ fromJust mref)-}

currC :: Value.PolicyId
currC = PolicyId{unPolicyId = "c7c9864fcc779b5573d97e3beefe5dd3705bbfe41972acd9bb6ebe9e"}

tnC :: Value.AssetName
tnC = AssetName "OtherToken"

defInitialDist :: Map Ledger.CardanoAddress Value.Value
defInitialDist =
  Map.fromList $
    (,( Value.lovelaceValueOf 99999900000000000
    --         <> Value.singleton currC tnC 1
      ))
      <$> E.knownAddresses

-- createToken
-- registerSymToken -?
-- 3rd arg to perform
{-
https://github.com/input-output-hk/quickcheck-contractmodel/blob/master/quickcheck-contractmodel/src/Test/QuickCheck/ContractModel.hs
createSymToken, registerSymToken, third argument to perform
https://github.com/Quviq/quickcheck-contractmodel-cooked/blob/35dfc688e3ea25fccc31314e8b6fc621241f5f15/cooked-contractmodel/test/Spec/Auction.hs#L99
https://github.com/Quviq/quickcheck-contractmodel-cooked/blob/35dfc688e3ea25fccc31314e8b6fc621241f5f15/cooked-contractmodel/test/Spec/Auction.hs#L185
https://github.com/Quviq/quickcheck-contractmodel-cooked/blob/35dfc688e3ea25fccc31314e8b6fc621241f5f15/cooked-contractmodel/test/Spec/Auction.hs#L190
 -}

prop_MultiSig :: Actions MultiSigModel -> Property
prop_MultiSig = E.propRunActionsWithOptions options

simpleVestTest :: DL MultiSigModel ()
simpleVestTest = do
  action $ Start 1 (Ada.adaValueOf 100)
  action $ Propose 2 (Ada.adaValueOf 10) 3 111111111111111111111111111
  action $ Add 4
  action $ Add 4
  action $ Add 5
  action $ Add 4
  action $ Cancel 2

{-
observeUTxOEscrow :: DL EscrowModel ()
observeUTxOEscrow = do
  action $ Pay w1 10
  observe "After payment" $ \_ cst -> numUTxOsAt addr cst == 1
  waitUntilDL 100
  action $ Refund w1
  observe "After refund" $ \_ cst -> numUTxOsAt addr cst == 0
  where
    addr = Scripts.validatorCardanoAddressAny Params.testnet $ typedValidator modelParams

    numUTxOsAt addr cst =
      Data.Foldable.length
        [ ()
        | TxOut (AddressInEra _ addr') _ _ _ <- Map.elems . unUTxO $ utxo cst
        , toAddressAny addr' == addr
        ]

prop_observeEscrow :: Property
prop_observeEscrow = forAllDL observeUTxOEscrow prop_Escrow

prop_Check :: QC.Property
prop_Check = QC.withMaxSuccess 1 $ forAllDL simpleVestTest prop_MultiSig
-}

prop_Check :: Property
prop_Check = forAllDL simpleVestTest prop_MultiSig

{-
finishEscrow :: DL EscrowModel ()
finishEscrow = do
  anyActions_
  finishingStrategy (const True)
  assertModel "Locked funds are not zero" (symIsZero . lockedValue)

finishingStrategy :: (Ledger.CardanoAddress -> Bool) -> DL EscrowModel ()
finishingStrategy walletAlive = do
  now <- viewModelState (currentSlot . to fromCardanoSlotNo)
  slot <- viewContractState refundSlot
  when (now < slot + 1) $ waitUntilDL $ fromIntegral $ slot + 1
  contribs <- viewContractState contributions
  Data.Foldable.sequence_
    [action $ Refund w | w <- testWallets, w `Map.member` contribs, walletAlive (walletAddress w)]

prop_FinishEscrow :: Property
prop_FinishEscrow = forAllDL finishEscrow prop_Escrow

noLockProof :: NoLockedFundsProof EscrowModel
noLockProof =
  defaultNLFP
    { nlfpMainStrategy = finishingStrategy (const True)
    , nlfpWalletStrategy = finishingStrategy . (==)
    }

prop_NoLockedFunds :: Property
prop_NoLockedFunds = checkNoLockedFundsProofWithOptions options noLockProof-}

{-
-- | Check that you can't redeem after the deadline and not refund before the deadline.
validityChecks :: ThreatModel ()
validityChecks = do
  let deadline = fromIntegral . TimeSlot.posixTimeToEnclosingSlot def $ escrowDeadline modelParams
      scriptAddr = Scripts.validatorCardanoAddressAny Params.testnet $ typedValidator modelParams
  input <- anyInputSuchThat $ (scriptAddr ==) . addressOf
  rmdr <- (fromData . toPlutusData =<<) <$> getRedeemer input
  case rmdr of
    Nothing -> fail "Missing or bad redeemer"
    Just Impl.Redeem ->
      shouldNotValidate $
        changeValidityRange
          ( TxValidityLowerBound AllegraEraOnwardsConway deadline
          , TxValidityUpperBound shelleyBasedEra Nothing
          )
    Just Impl.Refund ->
      shouldNotValidate $
        changeValidityRange
          ( TxValidityNoLowerBound
          , TxValidityUpperBound shelleyBasedEra (Just $ deadline - 1)
          )

prop_validityChecks :: Actions EscrowModel -> Property
prop_validityChecks = E.checkThreatModelWithOptions options validityChecks-}

prop_MultiSig_DoubleSatisfaction :: Actions MultiSigModel -> Property
prop_MultiSig_DoubleSatisfaction = E.checkDoubleSatisfactionWithOptions options

{-
prop_Escrow_DoubleSatisfaction :: Actions MultiSigModel -> Property
prop_Escrow_DoubleSatisfaction = E.checkDoubleSatisfactionWithOptions options
-}

tests :: TestTree
tests =
  testGroup
    "MultiSig"
    [ checkPredicateOptions
        options
        "can start"
        ( hasValidatedTransactionCountOfTotal 1 1
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-105)) -- <> Value.singleton currC tnC (-1)))
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 105)
    , checkPredicateOptions
        options
        "just start"
        ( hasValidatedTransactionCountOfTotal 12 12
        -- .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100)) -- <> Value.singleton currC tnC (-1)))
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 10123450)
          act $ Start 2 (Ada.adaValueOf 10123450)
          act $ Start 3 (Ada.adaValueOf 11234500)
          act $ Start 4 (Ada.adaValueOf 11234500)
          act $ Start 5 (Ada.adaValueOf 10123450)
          act $ Start 6 (Ada.adaValueOf 10123450)
          act $ Start 1 (Ada.adaValueOf 10123450)
          act $ Start 2 (Ada.adaValueOf 10123450)
          act $ Start 3 (Ada.adaValueOf 10123450)
          act $ Start 4 (Ada.adaValueOf 10123450)
          act $ Start 5 (Ada.adaValueOf 10123450)
          act $ Start 6 (Ada.adaValueOf 10123450)
    , checkPredicateOptions
        options
        "can propose"
        ( hasValidatedTransactionCountOfTotal 2 2
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100)) -- <> Value.singleton currC tnC (-1))
            -- .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf 10)
            .&&. walletFundsChange (walletAddress w2) mempty
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100)
          -- act $ Start 2 (Ada.adaValueOf 100 <> (assetClassValue tt 1))
          act $ Propose 2 (Ada.adaValueOf 10) 3 12345
    , checkPredicateOptions
        options
        "can add"
        ( hasValidatedTransactionCountOfTotal 4 4
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100)) -- <> Value.singleton currC tnC (-1)))
            -- .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf 10)
            -- .&&. walletFundsChange (walletAddress w3) mempty
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100)
          act $ Propose 2 (Ada.adaValueOf 10) 3 12345
          act $ Add 4
          act $ Add 5
    , checkPredicateOptions
        options
        "can pay"
        ( hasValidatedTransactionCountOfTotal 5 5
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100)) -- <> Value.singleton currC tnC (-1))
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 10)
            -- .&&. walletFundsChange (walletAddress w3) mempty
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100)
          act $ Propose 2 (Ada.adaValueOf 10) 3 12345
          act $ Add 5
          act $ Add 4
          act $ Pay 3
    , checkPredicateOptions
        options
        "can cancel"
        ( hasValidatedTransactionCountOfTotal 7 7
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100)) -- <> Value.singleton currC tnC (-1)))
            -- .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf 10)
            -- .&&. walletFundsChange (walletAddress w3) mempty
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100)
          act $ Propose 2 (Ada.adaValueOf 10) 3 1596059095001
          act $ Add 4
          act $ Add 4
          act $ Add 5
          act $ Add 4
          act $ Cancel 2
    , checkPredicateOptions
        options
        "can double pay"
        ( hasValidatedTransactionCountOfTotal 9 9
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100)) -- <> Value.singleton currC tnC (-1))
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf 30)
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 10)
            -- .&&. walletFundsChange (walletAddress w3) mempty
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100)
          act $ Propose 2 (Ada.adaValueOf 10) 3 12345
          act $ Add 4
          act $ Add 5
          act $ Pay 3
          act $ Propose 3 (Ada.adaValueOf 30) 2 12345
          act $ Add 5
          act $ Add 4
          act $ Pay 2
    , checkPredicateOptions
        options
        "can close"
        ( hasValidatedTransactionCountOfTotal 6 6
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100)) -- <> Value.singleton currC tnC (-1))
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 97)
            -- .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 10)
            -- .&&. walletFundsChange (walletAddress w3) mempty
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100)
          act $ Propose 2 (Ada.adaValueOf 97) 3 12345
          act $ Add 4
          act $ Add 5
          act $ Pay 3
          act $ Close 4
    , checkPredicateOptions
        options
        "can close and reopen and pay"
        ( hasValidatedTransactionCountOfTotal 12 12
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-200))
            -- .&&. walletFundsChange (walletAddress w6) (Value.adaValueOf (-100)) -- <> Value.singleton currC tnC (-1))
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 97)
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf 97)
            -- .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 10)
            -- .&&. walletFundsChange (walletAddress w3) mempty
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100)
          act $ Propose 2 (Ada.adaValueOf 97) 3 12345
          act $ Add 4
          act $ Add 5
          act $ Pay 3
          act $ Close 4
          act' (Start 1 (Ada.adaValueOf 100)) tt
          act' (Propose 4 (Ada.adaValueOf 97) 2 12345) tt'
          act' (Add 4) tt'
          act' (Add 5) tt'
          act' (Pay 2) tt'
          act' (Close 4) tt'
    , checkPredicateOptions
        options
        "can add many"
        (hasValidatedTransactionCountOfTotal 10 10)
        $ do
          act $ Start 1 (Ada.adaValueOf 100)
          act $ Propose 2 (Ada.adaValueOf 97) 3 12345
          act $ Add 5
          act $ Add 3
          act $ Add 3
          act $ Add 5
          act $ Add 5
          act $ Add 4
          act $ Add 5
          act $ Add 3
    , testProperty "QuickCheck ContractModel" $ QC.withMaxSuccess 100 (QC.noShrinking prop_MultiSig)
    --   , testProperty "QuickCheck CancelDL" (QC.expectFailure prop_Check)
    -- , testProperty "QuickCheck double satisfaction" $ prop_MultiSig_DoubleSatisfaction -}
    ]

{-    , testProperty "QuickCheck double satisfaction fails" $
        QC.expectFailure (QC.noShrinking prop_MultiSig_DoubleSatisfaction)-}
-- QC.verbose
{-

[
		[+] tok.var5 := Start 1 (Value {getValue = Map {unMap = [(,Map {unMap = [("",16400716675)]})]}}),
        [+]Propose 1 (Value {getValue = Map {unMap = [(,Map {unMap = [("",9572071720)]})]}}) 1 1596059147167,
        [+]Add 4,
        [+]Add 5,
        [+]Pay 4,
        [+]Propose 5 (Value {getValue = Map {unMap = [(,Map {unMap = [("",6687351965)]})]}}) 4 1596059151023,
        [+]Add 5,
        [+]Add 4,
        [+]Pay 3,
        [+]Propose 5 (Value {getValue = Map {unMap = [(,Map {unMap = [("",140359590)]})]}}) 3 1596059183434,
        [+]Add 4,
        [+]Add 3,
        [+]Pay 3
]

-}

checkPropMultiSigWithCoverage :: IO ()
checkPropMultiSigWithCoverage = do
  cr <-
    E.quickCheckWithCoverage QC.stdArgs options $ QC.withMaxSuccess 100 . E.propRunActionsWithOptions
  writeCoverageReport "MultiSig" cr

{-

{-
curSlot <- viewModelState currentSlot
      let deadline = toSlotNo . TimeSlot.posixTimeToEnclosingSlot lottoSlotConfig
                     $ TimeSlot.nominalDiffTimeToPOSIXTime (duration lottoSetup)-}

{-
instance RunModel MultiSigModel E.EmulatorM where
  perform _ cmd _ = lift $ voidCatch $ act cmd-}

voidCatch m = catchError (void m) (\ _ -> pure ())

-}

{-
import Control.Lens (At (at), makeLenses, to, (%=), (.=), (^.))
import Control.Monad (void, when)
import Control.Monad.Trans (lift)
import Data.Default (Default (def))
import Data.Foldable (Foldable (fold, length, null), sequence_)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import GHC.Generics (Generic)

import Cardano.Api.Shelley (toPlutusData)
import Cardano.Node.Emulator qualified as E
import Cardano.Node.Emulator.Internal.Node.Params qualified as Params
import Cardano.Node.Emulator.Internal.Node.TimeSlot qualified as TimeSlot
import Cardano.Node.Emulator.Test (
  checkPredicateOptions,
  hasValidatedTransactionCountOfTotal,
  walletFundsChange,
  (.&&.),
 )
import Cardano.Node.Emulator.Test.Coverage (writeCoverageReport)
import Cardano.Node.Emulator.Test.NoLockedFunds (
  NoLockedFundsProof (nlfpMainStrategy, nlfpWalletStrategy),
  checkNoLockedFundsProofWithOptions,
  defaultNLFP,
 )
import Ledger (Slot, minAdaTxOutEstimated, POSIXTime)
import Ledger qualified
import Ledger.Tx.CardanoAPI (fromCardanoSlotNo)
import Ledger.Typed.Scripts qualified as Scripts
import Ledger.Value.CardanoAPI qualified as Value
import Plutus.Script.Utils.Ada qualified as Ada
import Plutus.Script.Utils.Value (Value, geq, AssetClass, CurrencySymbol, TokenName, assetClass, assetClassValue, valueOf)
import PlutusLedgerApi.V1.Time (POSIXTime)

import Plutus.Examples.MultiSig hiding (Input(..), Label(..))
import Plutus.Examples.MultiSigAPI (
  --Params (..),
  propose,
  add,
  pay,
  cancel,
  start,
  --typedValidator,
 )
import Plutus.Examples.MultiSig qualified as Impl
import PlutusTx (fromData, Data)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Monoid (inv)

import Cardano.Api (
  AddressInEra (AddressInEra),
  AllegraEraOnwards (AllegraEraOnwardsConway),
  IsShelleyBasedEra (shelleyBasedEra),
  TxOut (TxOut),
  TxValidityLowerBound (TxValidityLowerBound, TxValidityNoLowerBound),
  TxValidityUpperBound (TxValidityUpperBound),
  UTxO (unUTxO),
  toAddressAny,
  PolicyId (..),
  AssetName (..)
 )
--import Cardano.Api.Script
import Test.QuickCheck qualified as QC hiding ((.&&.))
import Test.QuickCheck.ContractModel (
  Action,
  Actions,
  ContractModel,
  DL,
  RunModel,
  action,
  anyActions_,
  assertModel,
  contractState,
  currentSlot,
  deposit,
  forAllDL,
  lockedValue,
  observe,
  symIsZero,
  utxo,
  viewContractState,
  viewModelState,
  wait,
  waitUntilDL,
  withdraw,
 )
import Test.QuickCheck.ContractModel qualified as QCCM
import Test.QuickCheck.ContractModel.ThreatModel (
  IsInputOrOutput (addressOf),
  ThreatModel,
  anyInputSuchThat,
  changeValidityRange,
  getRedeemer,
  shouldNotValidate,
 )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (
  Property,
  choose,
  chooseInteger,
  frequency,
  testProperty,
 )

import Control.Monad.Except (catchError)

--import Plutus.Contract.Test.Certification
--import Plutus.Contract.Test.Certification.Run
import Test.QuickCheck.DynamicLogic qualified as QCD

-}

{-
curr :: CurrencySymbol
curr = "c7c9864fcc779b5573d97e3beefe5dd3705bbfe41972acd9bb6ebe9e"

tn :: TokenName
tn = "ThreadToken"

tt :: AssetClass
tt = assetClass curr tn

type Wallet = Integer

w1, w2, w3, w4, w5 :: Wallet
w1 = 1
w2 = 2
w3 = 3
w4 = 4
w5 = 5

walletAddress :: Wallet -> Ledger.CardanoAddress
walletAddress = (E.knownAddresses !!) . pred . fromIntegral

walletPrivateKey :: Wallet -> Ledger.PaymentPrivateKey
walletPrivateKey = (E.knownPaymentPrivateKeys !!) . pred . fromIntegral

testWallets :: [Wallet]
testWallets = [w1, w2, w3, w4, w5] -- removed five to increase collisions (, w6, w7, w8, w9, w10])

walletPaymentPubKeyHash :: Wallet -> Ledger.PaymentPubKeyHash
walletPaymentPubKeyHash =
  Ledger.PaymentPubKeyHash
    . Ledger.pubKeyHash
    . Ledger.unPaymentPubKey
    . (E.knownPaymentPublicKeys !!)
    . pred
    . fromIntegral

-}
