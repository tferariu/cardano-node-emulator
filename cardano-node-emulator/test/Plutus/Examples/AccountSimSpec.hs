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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- Test code for the Account Simulation on UTxO
module Plutus.Examples.AccountSimSpec (
  tests,
  prop_AccountSim,
  prop_Check,
  checkPropAccountSimWithCoverage,
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
import GHC.Generics (Generic)
import Ledger (Slot, minAdaTxOutEstimated)
import Ledger qualified
import Ledger.Tx.CardanoAPI (fromCardanoSlotNo)
import Ledger.Typed.Scripts qualified as Scripts
import Ledger.Value.CardanoAPI qualified as Value
import Plutus.Examples.AccountSim hiding (Input (..), Label (..), delete, insert, lookup)
import Plutus.Examples.AccountSim qualified as Impl
import Plutus.Examples.AccountSimAPI qualified as API
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
-- Generic helper functions and setup
------------------------------------------------------------------------------------------------------------------------------

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
testWallets = [w1, w2, w3, w4, w5]

walletPaymentPubKeyHash :: Wallet -> Ledger.PaymentPubKeyHash
walletPaymentPubKeyHash =
  Ledger.PaymentPubKeyHash
    . Ledger.pubKeyHash
    . Ledger.unPaymentPubKey
    . (E.knownPaymentPublicKeys !!)
    . pred
    . fromIntegral

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

{-
The token name and currency symbol needs to be extracted manually for the
unit tests. The written off-chain code produces errors that help get the
currency symbol if the validator or minting policy ever change. The quick-check
handles the Token using symbolic data.
-}
tn :: TokenName
tn = "ThreadToken"

curr :: CurrencySymbol
curr = "aead14eda6ba1867cc85c2754ed4d8b7646db7955880685d0aa7182b"

tt :: AssetClass
tt = assetClass curr tn

makeTT :: Ledger.TxOutRef -> AssetClass
makeTT oref = assetClass (curSymbol oref tn) tn

-- Similarly the TxIn of the UTxO spent to guarantee Thread Token Uniqueness is baked in
tin :: API.TxIn
tin = API.TxIn "b0de2873afe95a6530bf1ae88096cf43e17bb2ee669f9ba600838949ac1e08ec" (API.TxIx 5)

------------------------------------------------------------------------------------------------------------------------------
-- Code for generating quick-check tests and the model of the smart contract
------------------------------------------------------------------------------------------------------------------------------

data Phase
  = Initial
  | Running
  deriving (Show, Eq, Generic)

type Label = [(Wallet, Value)]

insert :: Wallet -> Value -> Label -> Label
insert w val [] = [(w, val)]
insert w val ((x, y) : xs) =
  if w == x then (w, val) : xs else (x, y) : insert w val xs

delete :: Wallet -> Label -> Label
delete w [] = []
delete w ((x, y) : xs) =
  if w == x then xs else (x, y) : delete w xs

lookup' :: Wallet -> Label -> Maybe Value
lookup' w [] = Nothing
lookup' w ((x, y) : xs) =
  if w == x then Just y else lookup' w xs

lookupGT :: Wallet -> Value -> Label -> Bool
lookupGT w v [] = False
lookupGT w v ((x, y) : xs) =
  if w == x then geq y v else lookupGT w v xs

lookupEmpty :: Wallet -> Label -> Bool
lookupEmpty w [] = False
lookupEmpty w ((x, y) : xs) =
  if w == x then y == (Ada.toValue 0) else lookupEmpty w xs

data AccountSimModel = AccountSimModel
  { _actualValue :: Value
  , _threadToken :: Maybe QCCM.SymToken
  , _txIn :: Maybe QCCM.SymTxIn
  , _phase :: Phase
  , _label :: Label
  }
  deriving (Eq, Show, Generic)

makeLenses ''AccountSimModel

options :: E.Options AccountSimModel
options =
  E.defaultOptions
    { E.initialDistribution = defInitialDist
    , E.params = Params.increaseTransactionLimits def
    , E.coverageIndex = Impl.covIdx
    }

genWallet :: QC.Gen Wallet
genWallet = QC.elements testWallets

instance ContractModel AccountSimModel where
  data Action AccountSimModel
    = Start Wallet
    | Open Wallet
    | Close Wallet
    | Withdraw Wallet Value
    | Deposit Wallet Value
    | Transfer Wallet Wallet Value
    | Cleanup Wallet
    deriving (Eq, Show, Generic)

  initialState =
    AccountSimModel
      { _actualValue = mempty
      , _threadToken = Nothing
      , _txIn = Nothing
      , _phase = Initial
      , _label = []
      }

  nextState a = void $ case a of
    Start w -> do
      phase .= Running
      actualValue .= (Ada.toValue 3000000)
      withdraw (walletAddress w) (Ada.toValue 3000000)
      symToken <- QCCM.createToken "thread token"
      threadToken .= Just symToken
      symTxIn <- QCCM.createTxIn "minting input"
      txIn .= Just symTxIn
      label .= []
      wait 1
    Open w -> do
      label' <- viewContractState label
      label .= insert w (Ada.toValue 0) label'
      wait 1
    Close w -> do
      label' <- viewContractState label
      label .= delete w label'
      wait 1
    Withdraw w v -> do
      actualValue' <- viewContractState actualValue
      actualValue .= actualValue' <> (PlutusTx.negate v)
      deposit (walletAddress w) v
      label' <- viewContractState label
      label .= insert w ((fromJust (lookup' w label')) PlutusTx.- v) label'
      wait 1
    Deposit w v -> do
      actualValue' <- viewContractState actualValue
      actualValue .= actualValue' <> v
      withdraw (walletAddress w) v
      label' <- viewContractState label
      label .= insert w ((fromJust (lookup' w label')) PlutusTx.+ v) label'
      wait 1
    Transfer from to v -> do
      label' <- viewContractState label
      let vF = fromJust (lookup' from label')
          vT = fromJust (lookup' to label')
      label .= insert from (vF PlutusTx.- v) (insert to (vT PlutusTx.+ v) label')
      wait 1
    Cleanup w -> do
      phase .= Initial
      actualValue' <- viewContractState actualValue
      deposit (walletAddress w) (actualValue')
      actualValue .= mempty
      threadToken .= Nothing
      wait 1

  precondition s a = case a of
    Start w -> currentPhase == Initial
    Open w -> currentPhase == Running && not (elem w accounts)
    Close w -> currentPhase == Running && lookupEmpty w accMap
    Withdraw w v -> currentPhase == Running && lookupGT w v accMap
    Deposit w v -> currentPhase == Running && elem w accounts
    Transfer from to v -> currentPhase == Running && lookupGT from v accMap && elem to accounts && from /= to
    Cleanup w -> currentPhase == Running && accMap == []
    where
      currentPhase = s ^. contractState . phase
      accMap = s ^. contractState . label
      accounts = map fst accMap

  validFailingAction _ _ = False

  arbitraryAction s =
    frequency
      [ (1, Start <$> genWallet)
      , (1, Open <$> genWallet)
      , (1, Close <$> genWallet)
      , (5, Cleanup <$> genWallet)
      , (6, genWithdrawAction)
      ,
        ( 3
        , Deposit
            <$> genWallet
            <*> ( Ada.lovelaceValueOf
                    <$> choose (Ada.getLovelace Ledger.minAdaTxOutEstimated, Ada.getLovelace (Ada.adaOf 100))
                )
        )
      , (2, genTransferAction)
      ]
    where
      accounts = s ^. contractState . label

      genWithdrawAction :: QC.Gen (Action AccountSimModel)
      genWithdrawAction = do
        w <- genWallet
        let max =
              ( case (lookup w accounts) of
                  Just v -> valueOf v Ada.adaSymbol Ada.adaToken
                  Nothing -> 0
              )
        pure (Withdraw w)
          <*> ( Ada.lovelaceValueOf
                  <$> choose ((Ada.getLovelace Ledger.minAdaTxOutEstimated), max)
              )

      genTransferAction :: QC.Gen (Action AccountSimModel)
      genTransferAction = do
        w <- genWallet
        let max =
              ( case (lookup w accounts) of
                  Just v -> valueOf v Ada.adaSymbol Ada.adaToken
                  Nothing -> 0
              )
        pure (Transfer w)
          <*> genWallet
          <*> ( Ada.lovelaceValueOf
                  <$> choose ((Ada.getLovelace Ledger.minAdaTxOutEstimated), max)
              )

act :: Action AccountSimModel -> E.EmulatorM ()
act = \case
  Start w ->
    void $
      API.start
        (walletAddress w)
        (walletPrivateKey w)
  Open w ->
    void $
      API.open
        (walletAddress w)
        (walletPrivateKey w)
        tt
  Close w ->
    void $
      API.close
        (walletAddress w)
        (walletPrivateKey w)
        tt
  Withdraw w v ->
    void $
      API.withdraw
        (walletAddress w)
        (walletPrivateKey w)
        v
        tt
  Deposit w v ->
    void $
      API.deposit
        (walletAddress w)
        (walletPrivateKey w)
        v
        tt
  Transfer from to v ->
    void $
      API.transfer
        (walletAddress from)
        (walletAddress to)
        (walletPrivateKey from)
        v
        tt
  Cleanup w ->
    void $
      API.cleanup
        (walletAddress w)
        (walletPrivateKey w)
        tt
        tin

instance RunModel AccountSimModel E.EmulatorM where
  perform s (Start w) translate = do
    (oref, tin) <- lift $ API.start (walletAddress w) (walletPrivateKey w)
    QCCM.registerToken "thread token" (toAssetId (makeTT oref))
    QCCM.registerTxIn "minting input" (tin)
  perform s (Open w) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      API.open
        (walletAddress w)
        (walletPrivateKey w)
        ttref
  perform s (Close w) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      API.close
        (walletAddress w)
        (walletPrivateKey w)
        ttref
  perform s (Withdraw w v) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      API.withdraw
        (walletAddress w)
        (walletPrivateKey w)
        v
        ttref
  perform s (Deposit w v) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      API.deposit
        (walletAddress w)
        (walletPrivateKey w)
        v
        ttref
  perform s (Transfer from to v) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      API.transfer
        (walletAddress from)
        (walletAddress to)
        (walletPrivateKey from)
        v
        ttref
  perform s (Cleanup w) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
        tinref = fromJust (translate <$> s ^. contractState . txIn)
    lift $
      API.cleanup
        (walletAddress w)
        (walletPrivateKey w)
        ttref
        tinref

------------------------------------------------------------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------------------------------------------------------------

defInitialDist :: Map Ledger.CardanoAddress Value.Value
defInitialDist =
  Map.fromList $
    (,(Value.lovelaceValueOf 99999900000000000))
      <$> E.knownAddresses

prop_AccountSim :: Actions AccountSimModel -> Property
prop_AccountSim = E.propRunActionsWithOptions options

simpleFailTest :: DL AccountSimModel ()
simpleFailTest = do
  action $ Start 1
  action $ Open 2
  action $ Close 3

prop_Check :: Property
prop_Check = forAllDL simpleFailTest prop_AccountSim

tests :: TestTree
tests =
  testGroup
    "AccountSim"
    [ checkPredicateOptions
        options
        "can start"
        ( hasValidatedTransactionCountOfTotal 1 1
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-3))
        )
        $ do
          act $ Start 1
    , checkPredicateOptions
        options
        "can open"
        ( hasValidatedTransactionCountOfTotal 2 2
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-3))
            .&&. walletFundsChange (walletAddress w2) mempty
        )
        $ do
          act $ Start 1
          act $ Open 1
    , checkPredicateOptions
        options
        "can open twice"
        ( hasValidatedTransactionCountOfTotal 3 3
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-3))
            .&&. walletFundsChange (walletAddress w2) mempty
        )
        $ do
          act $ Start 1
          act $ Open 2
          act $ Open 3
    , checkPredicateOptions
        options
        "can close"
        ( hasValidatedTransactionCountOfTotal 3 3
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-3))
        )
        $ do
          act $ Start 1
          act $ Open 2
          act $ Close 2
    , checkPredicateOptions
        options
        "can deposit"
        ( hasValidatedTransactionCountOfTotal 3 3
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-3))
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf (-10))
        )
        $ do
          act $ Start 1
          act $ Open 2
          act $ Deposit 2 (Ada.adaValueOf 10)
    , checkPredicateOptions
        options
        "can withdraw"
        ( hasValidatedTransactionCountOfTotal 4 4
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-3))
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf (-5))
        )
        $ do
          act $ Start 1
          act $ Open 2
          act $ Deposit 2 (Ada.adaValueOf 10)
          act $ Withdraw 2 (Ada.adaValueOf 5)
    , checkPredicateOptions
        options
        "can transfer"
        ( hasValidatedTransactionCountOfTotal 5 5
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-3))
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf (-10))
        )
        $ do
          act $ Start 1
          act $ Open 2
          act $ Deposit 2 (Ada.adaValueOf 10)
          act $ Open 3
          act $ Transfer 2 3 (Ada.adaValueOf 5)
    , checkPredicateOptions
        options
        "can close after ops"
        ( hasValidatedTransactionCountOfTotal 6 6
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-3))
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf (-10))
        )
        $ do
          act $ Start 1
          act $ Open 2
          act $ Deposit 2 (Ada.adaValueOf 10)
          act $ Open 3
          act $ Transfer 2 3 (Ada.adaValueOf 10)
          act $ Close 2
    , checkPredicateOptions
        options
        "can transfer out"
        ( hasValidatedTransactionCountOfTotal 7 7
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-3))
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf (-10))
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf (10))
        )
        $ do
          act $ Start 1
          act $ Open 2
          act $ Deposit 2 (Ada.adaValueOf 10)
          act $ Open 3
          act $ Transfer 2 3 (Ada.adaValueOf 10)
          act $ Close 2
          act $ Withdraw 3 (Ada.adaValueOf 10)
    , checkPredicateOptions
        options
        "can open all"
        ( hasValidatedTransactionCountOfTotal 6 6
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-3))
            .&&. walletFundsChange (walletAddress w2) mempty
        )
        $ do
          act $ Start 1
          act $ Open 5
          act $ Open 2
          act $ Open 4
          act $ Open 3
          act $ Open 1
    , checkPredicateOptions
        options
        "can open and deposit 1"
        ( hasValidatedTransactionCountOfTotal 7 7
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-3))
            .&&. walletFundsChange (walletAddress w5) (Value.adaValueOf (-10))
            .&&. walletFundsChange (walletAddress w2) mempty
        )
        $ do
          act $ Start 1
          act $ Open 5
          act $ Open 2
          act $ Open 4
          act $ Open 3
          act $ Deposit 5 (Ada.adaValueOf 10)
          act $ Open 1
    , checkPredicateOptions
        options
        "can start and cleanup"
        ( hasValidatedTransactionCountOfTotal 2 2
            .&&. walletFundsChange (walletAddress w1) mempty
        )
        $ do
          act $ Start 1
          act $ Cleanup 1
    , checkPredicateOptions
        options
        "can open, deposit, withdraw, close, cleanup"
        ( hasValidatedTransactionCountOfTotal 6 6
            .&&. walletFundsChange (walletAddress w1) mempty
            .&&. walletFundsChange (walletAddress w5) mempty
        )
        $ do
          act $ Start 1
          act $ Open 5
          act $ Deposit 5 (Ada.adaValueOf 10)
          act $ Withdraw 5 (Ada.adaValueOf 10)
          act $ Close 5
          act $ Cleanup 1
    , testProperty "QuickCheck ContractModel" $ QC.withMaxSuccess 100 (prop_AccountSim)
    , testProperty "QuickCheck CancelDL" (QC.expectFailure prop_Check)
    ]

checkPropAccountSimWithCoverage :: IO ()
checkPropAccountSimWithCoverage = do
  cr <-
    E.quickCheckWithCoverage QC.stdArgs options $ QC.withMaxSuccess 100 . E.propRunActionsWithOptions
  writeCoverageReport "AccountSim" cr
