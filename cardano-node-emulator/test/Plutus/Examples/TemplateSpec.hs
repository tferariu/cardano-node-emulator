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

-- Test code for the Template
module Plutus.Examples.TemplateSpec (
  tests,
  prop_Template,
  checkPropTemplateWithCoverage,
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
import Plutus.Examples.Template hiding (Input (..), Label (..), delete, insert, lookup)
import Plutus.Examples.Template qualified as Impl
import Plutus.Examples.TemplateAPI qualified as API
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

modelParams :: Params
modelParams =
  Params
    { optional = 0
    }

{-
The token name and currency symbol needs to be extracted manually for the
unit tests. The written off-chain code produces errors that help get the
currency symbol if the validator or minting policy ever change. The quick-check
handles the Token using symbolic data.
-}
tn :: TokenName
tn = "ThreadToken"

curr :: CurrencySymbol
curr = "86159a14814ec4708097bb0989028a651733335d8861ffcdadb27d31"

tt :: AssetClass
tt = assetClass curr tn

makeTT :: Ledger.TxOutRef -> AssetClass
makeTT oref = assetClass (curSymbol modelParams oref tn) tn

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

-- test model
data TemplateModel = TemplateModel
  { _actualValue :: Value
  , _threadToken :: Maybe QCCM.SymToken
  , _txIn :: Maybe QCCM.SymTxIn
  , _phase :: Phase
  }
  deriving (Eq, Show, Generic)

makeLenses ''TemplateModel

options :: E.Options TemplateModel
options =
  E.defaultOptions
    { E.initialDistribution = defInitialDist
    , E.params = Params.increaseTransactionLimits def
    , E.coverageIndex = Impl.covIdx
    }

genWallet :: QC.Gen Wallet
genWallet = QC.elements testWallets

-- actions for the model
instance ContractModel TemplateModel where
  data Action TemplateModel
    = Start Wallet
    | Close Wallet
    | Something Wallet Value
    deriving (Eq, Show, Generic)

  initialState =
    TemplateModel
      { _actualValue = mempty
      , _threadToken = Nothing
      , _txIn = Nothing
      , _phase = Initial
      }

  -- expected changes resulting from each action
  nextState a = void $ case a of
    Start w -> do
      phase .= Running
      actualValue .= (Ada.toValue 9000000)
      withdraw (walletAddress w) (Ada.toValue 9000000)
      symToken <- QCCM.createToken "thread token"
      threadToken .= Just symToken
      symTxIn <- QCCM.createTxIn "minting input"
      txIn .= Just symTxIn
      wait 1
    Close w -> do
      phase .= Initial
      actualValue' <- viewContractState actualValue
      deposit (walletAddress w) (actualValue')
      actualValue .= mempty
      threadToken .= Nothing
      wait 1
    Something w v -> do
      actualValue' <- viewContractState actualValue
      actualValue .= actualValue' <> (PlutusTx.negate v)
      deposit (walletAddress w) v
      wait 1

  -- when each action is possible
  precondition s a = case a of
    Start w -> currentPhase == Initial
    Something w v -> currentPhase == Running && (geq amount (v <> minValue))
    Close w -> currentPhase == Running
    where
      currentPhase = s ^. contractState . phase
      amount = (s ^. contractState . actualValue)

  validFailingAction _ _ = False

  -- generator for actions
  arbitraryAction s =
    frequency
      [ (1, Start <$> genWallet)
      , (1, Close <$> genWallet)
      , (6, genSomethingAction)
      ]
    where
      genSomethingAction :: QC.Gen (Action TemplateModel)
      genSomethingAction = do
        w <- genWallet
        pure (Something w)
          <*> ( Ada.lovelaceValueOf
                  <$> choose (3000000, 6000000)
              )

-- endpoint to run manual tests
act :: Action TemplateModel -> E.EmulatorM ()
act = \case
  Start w ->
    void $
      API.start
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
  Close w ->
    void $
      API.close
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tt
        tin
  Something w v ->
    void $
      API.doSomething
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        v
        tt

-- describes which model action corresponds with which API transaction being submitted
instance RunModel TemplateModel E.EmulatorM where
  perform s (Start w) translate = do
    (oref, tin) <- lift $ API.start (walletAddress w) (walletPrivateKey w) modelParams
    -- using the Symbolic function of the model to register minting data
    QCCM.registerToken "thread token" (toAssetId (makeTT oref))
    QCCM.registerTxIn "minting input" (tin)
  perform s (Something w v) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      API.doSomething
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        v
        ttref
  perform s (Close w) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
        -- extracting the TxIn from the symbolic version in the models
        tinref = fromJust (translate <$> s ^. contractState . txIn)
    lift $
      API.close
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
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

-- property for running the QuickCheck model
prop_Template :: Actions TemplateModel -> Property
prop_Template = E.propRunActionsWithOptions options

-- several manual tests followed by QuickCheck generated model tests
tests :: TestTree
tests =
  testGroup
    "Template"
    [ checkPredicateOptions
        options
        "can start"
        ( hasValidatedTransactionCountOfTotal 1 1
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-9))
        )
        $ do
          act $ Start 1
    , checkPredicateOptions
        options
        "can close"
        ( hasValidatedTransactionCountOfTotal 2 2
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-9))
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf (9))
        )
        $ do
          act $ Start 1
          act $ Close 2
    , checkPredicateOptions
        options
        "can do something and close"
        ( hasValidatedTransactionCountOfTotal 3 3
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-9))
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf (5))
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf (4))
        )
        $ do
          act $ Start 1
          act $ Something 2 (Ada.adaValueOf 5)
          act $ Close 3
    , testProperty "QuickCheck ContractModel" $ QC.withMaxSuccess 100 (prop_Template)
    ]

checkPropTemplateWithCoverage :: IO ()
checkPropTemplateWithCoverage = do
  cr <-
    E.quickCheckWithCoverage QC.stdArgs options $ QC.withMaxSuccess 100 . E.propRunActionsWithOptions
  writeCoverageReport "Template" cr
