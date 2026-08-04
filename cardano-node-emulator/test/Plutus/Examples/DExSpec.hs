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

-- Test code for the Limit Order Book Distributed Exchange
module Plutus.Examples.DExSpec (
  tests,
  prop_DEx,
  checkPropDExWithCoverage,
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
import Ledger (Slot, minAdaTxOutEstimated)
import Ledger qualified
import Ledger.Tx.CardanoAPI (fromCardanoSlotNo)
import Ledger.Typed.Scripts qualified as Scripts
import Ledger.Value.CardanoAPI qualified as Value
import Plutus.Examples.DEx hiding (Label (..), Redeemer (..))
import Plutus.Examples.DEx qualified as Impl
import Plutus.Examples.DExAPI (
  exchange,
  getPayAmt,
  paymentValue,
  start,
  stop,
  unite,
  update,
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
import PlutusTx.Ratio
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

-- Dummy tokens to be used in the exchange
scs :: CurrencySymbol
scs = "1111864fcc779b5373d97e3beefe5dd3705bbfe41972acd9bb6ebe9e"

stn :: TokenName
stn = "SellToken"

stok :: AssetClass
stok = assetClass scs stn

bcs :: CurrencySymbol
bcs = "2222864fcc779b5373d97e3beefe5dd3705bbfe41972acd9bb6ebe9e"

btn :: TokenName
btn = "BuyToken"

btok :: AssetClass
btok = assetClass bcs btn

genST :: QC.Gen AssetClass
genST = QC.elements [stok]

genBT :: QC.Gen AssetClass
genBT = QC.elements [btok]

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
    { sellCurr = stok
    , buyCurr = btok
    }

tn :: TokenName
tn = "ThreadToken"

curr :: CurrencySymbol
curr = "45ae8b2f2474cb9fde4d2e7b3f6511adbbe051a2d9dcfb80fa75569e"

-- Two Thread Tokens are necessary if you open two different instances of the contract
tn' :: TokenName
tn' = "ThreadToken"

curr' :: CurrencySymbol
curr' = "302ab3c023d2d3a2ca0fd2d25b8ca68725bd05b4f88cbde01cade0a1"

tin :: API.TxIn
tin = API.TxIn "a1ad2a0753129bc558b039ed06b7373de2847e72c2ec7bccf89afd442ccf3f5d" (API.TxIx 5)

-- A second TxIn for the second Thread Token is also necessary
tin' :: API.TxIn
tin' = API.TxIn "9b46c94581afc2e1e81e9cacfd0cf734b6b8512bade903cd88e9b59b5e192045" (API.TxIx 1)

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

paymentValue' :: AssetClass -> Integer -> Value.Value
paymentValue' ac amt = Value.singleton (toPolicyId (fst (unAssetClass ac))) (toAssetName (snd (unAssetClass ac))) amt

------------------------------------------------------------------------------------------------------------------------------
-- Code for generating quick-check tests and the model of the smart contract
------------------------------------------------------------------------------------------------------------------------------

data Phase
  = Stopped
  | Running
  deriving (Show, Eq, Generic)

data DExState = DExState
  { _actualValue :: Value
  , _buyAC :: Maybe AssetClass
  , _sellAC :: Maybe AssetClass
  , _threadToken :: Maybe QCCM.SymToken
  , _txIn :: Maybe QCCM.SymTxIn
  , _phase :: Phase
  , _rate :: Maybe PlutusTx.Ratio.Rational
  , _owner :: Maybe Wallet
  , _count :: [(Wallet, Integer)]
  }
  deriving (Eq, Show, Generic)

makeLenses ''DExState

defInitialDist :: Map Ledger.CardanoAddress Value.Value
defInitialDist =
  Map.fromList $
    (,( Value.lovelaceValueOf 99999900000000000
          <> Value.singleton (toPolicyId scs) (toAssetName stn) 1000000
          <> Value.singleton (toPolicyId bcs) (toAssetName btn) 1000000
      ))
      <$> E.knownAddresses

options :: E.Options DExState
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

increment :: Wallet -> [(Wallet, Integer)] -> [(Wallet, Integer)]
increment w [] = [(w, 1)]
increment w ((x, y) : xs) =
  if w == x then (w, y + 1) : xs else (x, y) : increment w xs

reset :: Wallet -> [(Wallet, Integer)] -> [(Wallet, Integer)]
reset w [] = [(w, 0)]
reset w ((x, y) : xs) =
  if w == x then (w, 0) : xs else (x, y) : reset w xs

getCount :: Wallet -> [(Wallet, Integer)] -> Integer
getCount w [] = 0
getCount w ((x, y) : xs) =
  if w == x then y else getCount w xs

instance ContractModel DExState where
  data Action DExState
    = Update Wallet Value PlutusTx.Ratio.Rational
    | Exchange Integer Wallet
    | Start Wallet Value PlutusTx.Ratio.Rational AssetClass AssetClass
    | Stop Wallet
    | Unite Wallet
    deriving (Eq, Show, Generic)

  initialState =
    DExState
      { _actualValue = mempty
      , _buyAC = Nothing
      , _sellAC = Nothing
      , _threadToken = Nothing
      , _txIn = Nothing
      , _phase = Stopped
      , _rate = Nothing
      , _owner = Nothing
      , _count = [(w1, 0), (w2, 0), (w3, 0), (w4, 0), (w5, 0), (w6, 0)]
      }

  nextState a = void $ case a of
    Unite w -> do
      count' <- viewContractState count
      phase' <- viewContractState phase
      count .= reset w count'
      phase .= phase'
      wait 1
    Update w v r -> do
      actualValue' <- viewContractState actualValue
      withdraw
        (walletAddress w)
        (v <> (PlutusTx.negate actualValue'))
      actualValue .= v
      count' <- viewContractState count
      phase .= Running
      count .= increment w count'
      owner .= Just w
      rate .= Just r
      wait 1
    Exchange amt w -> do
      actualValue' <- viewContractState actualValue
      owner' <- viewContractState owner
      buyCurr' <- viewContractState buyAC
      sellCurr' <- viewContractState sellAC
      rate' <- viewContractState rate
      count' <- viewContractState count
      phase .= Running
      count .= increment (fromJust owner') (increment w count')
      deposit (walletAddress w) (paymentValue' (fromJust sellCurr') amt)
      withdraw (walletAddress w) (lovelaceValue 3_000_000)
      withdraw (walletAddress w) (paymentValue' (fromJust buyCurr') (getPayAmt amt (fromJust rate')))
      deposit
        (walletAddress (fromJust owner'))
        (paymentValue' (fromJust buyCurr') (getPayAmt amt (fromJust rate')))
      deposit (walletAddress (fromJust owner')) (lovelaceValue 3_000_000)
      actualValue
        .= actualValue'
          <> ( PlutusTx.negate
                ( paymentValue
                    (fst (unAssetClass (fromJust sellCurr')))
                    (snd (unAssetClass (fromJust sellCurr')))
                    amt
                )
             )
      wait 1
    Start w v r bac sac -> do
      phase .= Running
      withdraw (walletAddress w) (v)
      actualValue .= v
      symToken <- QCCM.createToken "thread token"
      threadToken .= Just symToken
      symTxIn <- QCCM.createTxIn "minting input"
      txIn .= Just symTxIn
      owner .= Just w
      rate .= Just r
      buyAC .= Just bac
      sellAC .= Just sac
      wait 1
    Stop w -> do
      count' <- viewContractState count
      phase .= Stopped
      count .= increment w count'
      actualValue' <- viewContractState actualValue
      deposit (walletAddress w) (actualValue')
      actualValue .= emptyValue
      threadToken .= Nothing
      txIn .= Nothing
      owner .= Nothing
      rate .= Nothing
      buyAC .= Nothing
      sellAC .= Nothing
      wait 1

  precondition s a = case a of
    Unite w -> ((getCount w count') >= 3)
    Update w v r -> currentPhase == Running && (w == owner') && ((getCount w count') < 3)
    Exchange amt w ->
      currentPhase == Running
        && (w /= owner')
        && ((getCount w count') < 3)
        && (amt' > amt + 500)
    Start w v r bac sac -> currentPhase == Stopped && ((getCount w count') < 3)
    Stop w -> currentPhase == Running && (w == owner') && ((getCount w count') < 3)
    where
      currentPhase = s ^. contractState . phase
      currentValue = (s ^. contractState . actualValue)
      owner' = fromJust $ (s ^. contractState . owner)
      sellCurr = fromJust $ (s ^. contractState . sellAC)
      count' = s ^. contractState . count
      amount = (s ^. contractState . actualValue)
      curr = stok
      amt' = valueOf amount (fst (unAssetClass curr)) (snd (unAssetClass curr))

  validFailingAction _ _ = False

  arbitraryAction s =
    frequency
      [
        ( 10
        , Update
            <$> genWallet
            <*> genValue
            <*> (fromJust <$> (ratio <$> chooseInteger (1, 10) <*> chooseInteger (1, 10)))
        )
      , (10, Exchange <$> chooseInteger (500, amt) <*> genWallet) -- keep checking with 1
      , (1, Stop <$> genWallet)
      , (5, Unite <$> genWallet)
      ,
        ( 2
        , Start
            <$> genWallet
            <*> genValue
            <*> (fromJust <$> (ratio <$> chooseInteger (1, 10) <*> chooseInteger (1, 10)))
            <*> genBT
            <*> genST
        )
      ]
    where
      amount = (s ^. contractState . actualValue)
      curr = stok
      amt = valueOf amount (fst (unAssetClass curr)) (snd (unAssetClass curr))

      genValue :: QC.Gen Value
      genValue = do
        ada <- choose (3_000_000, 100_000_000)
        amt <- choose (2000, 5000)
        pure
          (Ada.lovelaceValueOf ada <> paymentValue (fst (unAssetClass curr)) (snd (unAssetClass curr)) amt)

act :: Action DExState -> E.EmulatorM ()
act = \case
  Update w v r ->
    void $
      update
        (walletAddress w)
        v
        r
        (walletPrivateKey w)
        modelParams
        tt
  Exchange amt w ->
    void $
      exchange
        (walletAddress w)
        amt
        (walletPrivateKey w)
        modelParams
        tt
  Start w v r bc sc ->
    void $
      start
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        v
        r
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
  Unite w ->
    void $
      unite
        (walletAddress w)
        (walletPrivateKey w)

instance RunModel DExState E.EmulatorM where
  perform s (Start w v r bac sac) translate = do
    (oref, tin, tout) <- lift $ start (walletAddress w) (walletPrivateKey w) modelParams v r False
    QCCM.registerToken "thread token" (toAssetId (makeTT oref))
    QCCM.registerTxIn "minting input" (tin)
  perform s (Exchange amt w) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      exchange
        (walletAddress w)
        amt
        (walletPrivateKey w)
        modelParams
        ttref
  perform s (Update w v r) translate = void $ do
    let ttref = fromAssetId (fromJust (translate <$> s ^. contractState . threadToken))
    lift $
      update
        (walletAddress w)
        (v <> paymentValue (fst (unAssetClass ttref)) (snd (unAssetClass ttref)) 1)
        r
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
  perform s (Unite w) translate = void $ do
    lift $
      unite
        (walletAddress w)
        (walletPrivateKey w)

------------------------------------------------------------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------------------------------------------------------------

prop_DEx :: Actions DExState -> Property
prop_DEx = E.propRunActionsWithOptions options

tests :: TestTree
tests =
  testGroup
    "DEx"
    [ checkPredicateOptions
        options
        "can start"
        ( hasValidatedTransactionCountOfTotal 1 1
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100) <> paymentValue' stok (-1000))
        )
        $ do
          act $
            Start
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 1000
              )
              (fromJust (ratio 1 2))
              stok
              btok
    , checkPredicateOptions
        options
        "can Update"
        ( hasValidatedTransactionCountOfTotal 2 2
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100) <> paymentValue' stok (-1900))
        )
        $ do
          act $
            Start
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 1000
              )
              (fromJust (ratio 1 2))
              stok
              btok
          act $
            Update
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 1900
                  <> paymentValue (fst (unAssetClass tt)) (snd (unAssetClass tt)) 1
              )
              (fromJust (ratio 3 4))
    , checkPredicateOptions
        options
        "can Multiple Update"
        ( hasValidatedTransactionCountOfTotal 3 3
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-50) <> paymentValue' stok (-5))
        )
        $ do
          act $
            Start
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 1000
              )
              (fromJust (ratio 1 2))
              stok
              btok
          act $
            Update
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 1900
                  <> paymentValue (fst (unAssetClass tt)) (snd (unAssetClass tt)) 1
              )
              (fromJust (ratio 3 4))
          act $
            Update
              1
              ( Ada.adaValueOf 50
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 5
                  <> paymentValue (fst (unAssetClass tt)) (snd (unAssetClass tt)) 1
              )
              (fromJust (ratio 3 1))
    , checkPredicateOptions
        options
        "can Exchange"
        ( hasValidatedTransactionCountOfTotal 2 2
            .&&. walletFundsChange
              (walletAddress w1)
              ( Value.adaValueOf (-97)
                  <> paymentValue' stok (-1000)
                  <> paymentValue' btok (50)
              )
            .&&. walletFundsChange
              (walletAddress w2)
              ( Value.adaValueOf (-3)
                  <> paymentValue' stok (100)
                  <> paymentValue' btok (-50)
              )
        )
        $ do
          act $
            Start
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 1000
              )
              (fromJust (ratio 1 2))
              stok
              btok
          act $ Exchange 100 2
    , checkPredicateOptions
        options
        "can Multiple Exchange"
        ( hasValidatedTransactionCountOfTotal 4 4
            .&&. walletFundsChange
              (walletAddress w1)
              (Value.adaValueOf (-91) <> paymentValue' stok (-1000) <> paymentValue' btok (150))
            .&&. walletFundsChange
              (walletAddress w2)
              (Value.adaValueOf (-3) <> paymentValue' btok (-50) <> paymentValue' stok (100))
            .&&. walletFundsChange
              (walletAddress w6)
              (Value.adaValueOf (-3) <> paymentValue' btok (-50) <> paymentValue' stok (100))
            .&&. walletFundsChange
              (walletAddress w4)
              (Value.adaValueOf (-3) <> paymentValue' btok (-50) <> paymentValue' stok (100))
        )
        $ do
          act $
            Start
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 1000
              )
              (fromJust (ratio 1 2))
              stok
              btok
          act $ Exchange 100 2
          act $ Exchange 100 6
          act $ Exchange 100 4
    , checkPredicateOptions
        options
        "can Stop"
        ( hasValidatedTransactionCountOfTotal 2 2
            .&&. walletFundsChange (walletAddress w1) mempty
        )
        $ do
          act $
            Start
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 1000
              )
              (fromJust (ratio 1 2))
              stok
              btok
          act $ Stop 1
    , checkPredicateOptions
        options
        "can Restart"
        ( hasValidatedTransactionCountOfTotal 3 3
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100) <> paymentValue' stok (-1000))
        )
        $ do
          act $
            Start
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 1000
              )
              (fromJust (ratio 1 2))
              stok
              btok
          act $ Stop 1
          act $
            Start
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 1000
              )
              (fromJust (ratio 1 2))
              stok
              btok
    , checkPredicateOptions
        options
        "can do All"
        ( hasValidatedTransactionCountOfTotal 5 5
            .&&. walletFundsChange
              (walletAddress w1)
              ( Value.adaValueOf (6)
                  <> paymentValue' stok (-1300)
                  <> paymentValue' btok (1400)
              )
            .&&. walletFundsChange
              (walletAddress w2)
              ( Value.adaValueOf (-3)
                  <> paymentValue' stok (1000)
                  <> paymentValue' btok (-500)
              )
            .&&. walletFundsChange
              (walletAddress w5)
              ( Value.adaValueOf (-3)
                  <> paymentValue' stok (300)
                  <> paymentValue' btok (-900)
              )
        )
        $ do
          act $
            Start
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 1001
              )
              (fromJust (ratio 1 2))
              stok
              btok
          act $ Exchange 1000 2
          act $
            Update
              1
              ( Ada.adaValueOf 100
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 901
                  <> paymentValue (fst (unAssetClass tt)) (snd (unAssetClass tt)) 1
              )
              (fromJust (ratio 9 3))
          act $ Exchange 300 5
          act $ Stop 1
    , checkPredicateOptions
        options
        "Specific Update"
        ( hasValidatedTransactionCountOfTotal 7 7
        )
        $ do
          act $
            Start
              1
              ( Ada.adaValueOf 12
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 4474
              )
              (fromJust (ratio 1 7))
              stok
              btok
          act $ Exchange 262 5
          act $ Exchange 134 5
          act $
            Update
              1
              ( Ada.adaValueOf 36
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 4926
                  <> paymentValue (fst (unAssetClass tt)) (snd (unAssetClass tt)) 1
              )
              (fromJust (ratio 6 5))
          act $ Exchange 262 5
          act $ Exchange 134 5
          act $ Unite 5
    , checkPredicateOptions
        options
        "Specific Exchange"
        ( hasValidatedTransactionCountOfTotal 3 3
        )
        $ do
          act $
            Start
              1
              ( Ada.lovelaceValueOf 78833384
                  <> paymentValue (fst (unAssetClass stok)) (snd (unAssetClass stok)) 2403
              )
              (fromJust (ratio 1 1))
              stok
              btok
          act $ Exchange 598 3
          act $ Exchange 1051 2
    , testProperty "QuickCheck ContractModel" $ QC.withMaxSuccess 100 (QC.noShrinking prop_DEx)
    ]

checkPropDExWithCoverage :: IO ()
checkPropDExWithCoverage = do
  cr <-
    E.quickCheckWithCoverage QC.stdArgs options $ QC.withMaxSuccess 100 . E.propRunActionsWithOptions
  writeCoverageReport "DEx" cr
