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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- Test code for the Multi Signature Wallet
module Plutus.Examples.MultiSigSpec (
  tests,
  prop_MultiSig,
  prop_Check,
  checkPropMultiSigWithCoverage,
) where

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
import Cardano.Api qualified as API
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
import Control.Lens (At (at), makeLenses, to, (%=), (.=), (^.))
import Control.Monad (void, when)
import Control.Monad.Trans (lift)
import Data.Default (Default (def))
import Data.Foldable (Foldable (fold, length, null), sequence_)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Debug.Trace
import GHC.Generics (Generic)
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
import Plutus.Examples.MultiSig hiding (Label (..), Redeemer (..))
import Plutus.Examples.MultiSig qualified as Impl
import Plutus.Examples.MultiSigAPI (
  add,
  cancel,
  pay,
  propose,
  start,
  stop,
 )
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
import PlutusTx (fromData)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Monoid (inv)
import PlutusTx.Prelude qualified as PlutusTx
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

------------------------------------------------------------------------------------------------------------------------------
-- Helper functions and setup
------------------------------------------------------------------------------------------------------------------------------

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
testWallets = [w1, w2, w3, w4, w5, w6]

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
    , minSigs = 2
    , maxWait = 2000000000
    }

tn :: TokenName
tn = "ThreadToken"

curr :: CurrencySymbol
curr = "fade0b5e4a2d377395acc104fd6fd59ef5fa397a0c786ec8a98dee19"

tn' :: TokenName
tn' = "ThreadToken"

curr' :: CurrencySymbol
curr' = "60e0473cfd214b4af56dc2b0f2e9108224bb92be1d8a59bcdf9a8646"

tin :: API.TxIn
tin = API.TxIn "b0de2873afe95a6530bf1ae88096cf43e17bb2ee669f9ba600838949ac1e08ec" (API.TxIx 5)

tin' :: API.TxIn
tin' = API.TxIn "c1e3734ceec1b6f7c1959def2a12a8cf7d1aaf7ee15f42e88df09513f6a6ff28" (API.TxIx 1)

-- Debug Switches
ok :: Bool
ok = False

ok' :: Bool
ok' = False

tt :: AssetClass
tt = assetClass curr tn

tt' :: AssetClass
tt' = assetClass curr' tn'

makeTT :: Ledger.TxOutRef -> AssetClass
makeTT oref = assetClass (curSymbol modelParams oref tn) tn

beginningOfTime :: Integer
beginningOfTime = 1596059091000

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

toAssetName :: TokenName -> API.AssetName
toAssetName (TokenName bs) = API.AssetName $ Builtins.fromBuiltin bs

fromAssetId :: API.AssetId -> AssetClass
fromAssetId API.AdaAssetId = AssetClass (Ada.adaSymbol, Ada.adaToken)
fromAssetId (API.AssetId policy name) = AssetClass (fromPolicyId policy, fromAssetName name)

fromPolicyId :: API.PolicyId -> CurrencySymbol
fromPolicyId (API.PolicyId hash) = CurrencySymbol . Builtins.toBuiltin $ API.serialiseToRawBytes hash

fromAssetName :: API.AssetName -> TokenName
fromAssetName (API.AssetName bs) = TokenName $ Builtins.toBuiltin bs

------------------------------------------------------------------------------------------------------------------------------
-- Code for generating quick-check tests and the model of the smart contract
------------------------------------------------------------------------------------------------------------------------------

data Phase
  = Initial
  | Holding
  | Collecting
  deriving (Show, Eq, Generic)

data MultiSigState = MultiSigState
  { _actualValue :: Value
  , _allowedSignatories :: [Wallet]
  , _requiredSignatories :: Integer
  , _threadToken :: Maybe QCCM.SymToken
  , _txIn :: Maybe QCCM.SymTxIn
  , _phase :: Phase
  , _paymentValue :: Value
  , _paymentTarget :: Maybe Wallet
  , _deadline :: Maybe Integer
  , _actualSignatories :: [Wallet]
  }
  deriving (Eq, Show, Generic)

makeLenses ''MultiSigState

options :: E.Options MultiSigState
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

instance ContractModel MultiSigState where
  data Action MultiSigState
    = Propose Wallet Value Wallet Integer
    | Add Wallet
    | Pay Wallet
    | Cancel Wallet
    | Start Wallet Value
    | Stop Wallet
    deriving (Eq, Show, Generic)

  initialState =
    MultiSigState
      { _actualValue = mempty
      , _allowedSignatories = [w5, w3, w4]
      , _requiredSignatories = (minSigs modelParams)
      , _threadToken = Nothing
      , _phase = Initial
      , _paymentValue = emptyValue
      , _paymentTarget = Nothing
      , _deadline = Nothing
      , _actualSignatories = []
      , _txIn = Nothing
      }

  nextState a = void $ case a of
    Propose w1 v w2 d -> do
      phase .= Collecting
      paymentValue .= v
      paymentTarget .= Just w2
      deadline .= Just d
      wait 1
    Add w -> do
      actualSignatories' <- viewContractState actualSignatories
      actualSignatories
        %= ( case (elem w actualSignatories') of
              True -> id
              False -> (w :)
           )
      wait 1
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
      withdraw (walletAddress w) (v)
      actualValue .= v
      symToken <- QCCM.createToken "thread token"
      threadToken .= Just symToken
      symTxIn <- QCCM.createTxIn "minting input"
      txIn .= Just symTxIn
      actualSignatories .= []
      wait 1
    Stop w -> do
      phase .= Initial
      actualValue' <- viewContractState actualValue
      deposit (walletAddress w) (actualValue')
      actualValue .= mempty
      threadToken .= Nothing
      actualSignatories .= []
      wait 1

  precondition s a = case a of
    Propose w1 v w2 d -> currentPhase == Holding && (currentValue `geq` v) && (v `geq` minValue)
    Add w -> currentPhase == Collecting && (elem w sigs)
    Pay w -> currentPhase == Collecting && ((length actualSigs) >= (fromIntegral min)) && w == receiver
    Cancel w -> currentPhase == Collecting && ((d + 2000) < timeInt)
    Start w v -> currentPhase == Initial && (v `geq` x2MinValue)
    Stop w -> currentPhase == Holding && ((Ada.toValue Ledger.minAdaTxOutEstimated) `gt` currentValue)
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

  validFailingAction _ _ = False

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
      , (3, Stop <$> genWallet)
      ]
    where
      amount = (s ^. contractState . actualValue)
      slot = s ^. currentSlot . to fromCardanoSlotNo
      time = TimeSlot.slotToEndPOSIXTime def slot
      timeInt = Ledger.getPOSIXTime time

-- for the first/only smart contract instance, baking in the thread token is fine
act :: Action MultiSigState -> E.EmulatorM ()
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
  Stop w ->
    void $
      stop
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tt
        tin
        False

-- For multiple instances we need to specify the thread token of the current contract being used.
act' :: Action MultiSigState -> AssetClass -> E.EmulatorM ()
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
  Stop w ->
    void $
      stop
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tok
        tin'
        ok'

instance RunModel MultiSigState E.EmulatorM where
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
  perform s (Stop w) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
        tinref = fromJust (translate <$> s ^. contractState . txIn)
    lift $
      stop
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        ttref
        tinref
        False

------------------------------------------------------------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------------------------------------------------------------

defInitialDist :: Map Ledger.CardanoAddress Value.Value
defInitialDist =
  Map.fromList $
    (,( Value.lovelaceValueOf 99999900000000000
      ))
      <$> E.knownAddresses

prop_MultiSig :: Actions MultiSigState -> Property
prop_MultiSig = E.propRunActionsWithOptions options

simpleVestTest :: DL MultiSigState ()
simpleVestTest = do
  action $ Start 1 (Ada.adaValueOf 100)
  action $ Propose 2 (Ada.adaValueOf 10) 3 111111111111111111111111111
  action $ Add 4
  action $ Add 4
  action $ Add 5
  action $ Add 4
  action $ Cancel 2

prop_Check :: Property
prop_Check = forAllDL simpleVestTest prop_MultiSig

tests :: TestTree
tests =
  testGroup
    "MultiSig"
    [ checkPredicateOptions
        options
        "can start"
        ( hasValidatedTransactionCountOfTotal 1 1
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-105))
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 105)
    , checkPredicateOptions
        options
        "just start"
        (hasValidatedTransactionCountOfTotal 12 12)
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
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100))
            .&&. walletFundsChange (walletAddress w2) mempty
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100)
          act $ Propose 2 (Ada.adaValueOf 10) 3 12345
    , checkPredicateOptions
        options
        "can add"
        ( hasValidatedTransactionCountOfTotal 4 4
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100))
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
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100))
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 10)
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
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100))
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
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100))
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf 30)
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 10)
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
        "can Stop"
        ( hasValidatedTransactionCountOfTotal 6 6
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100))
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 97)
            .&&. walletFundsChange (walletAddress w4) (Value.adaValueOf 3)
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100)
          act $ Propose 2 (Ada.adaValueOf 97) 3 12345
          act $ Add 4
          act $ Add 5
          act $ Pay 3
          act $ Stop 4
    , checkPredicateOptions
        options
        "can stop and reopen and pay"
        ( hasValidatedTransactionCountOfTotal 12 12
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-200))
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 97)
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf 97)
            .&&. walletFundsChange (walletAddress w4) (Value.adaValueOf 6)
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100)
          act $ Propose 2 (Ada.adaValueOf 97) 3 12345
          act $ Add 4
          act $ Add 5
          act $ Pay 3
          act $ Stop 4
          act' (Start 1 (Ada.adaValueOf 100)) tt'
          act' (Propose 4 (Ada.adaValueOf 97) 2 12345) tt'
          act' (Add 4) tt'
          act' (Add 5) tt'
          act' (Pay 2) tt'
          act' (Stop 4) tt'
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
    ]

checkPropMultiSigWithCoverage :: IO ()
checkPropMultiSigWithCoverage = do
  cr <-
    E.quickCheckWithCoverage QC.stdArgs options $ QC.withMaxSuccess 100 . E.propRunActionsWithOptions
  writeCoverageReport "MultiSig" cr
