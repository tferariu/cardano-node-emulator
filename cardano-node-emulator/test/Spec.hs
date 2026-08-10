{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Main (main) where

import Test.Tasty (TestTree, defaultMain, testGroup)

import Cardano.Node.Emulator.GeneratorsSpec qualified as GeneratorsSpec
import Cardano.Node.Emulator.MTLSpec qualified as MTLSpec
import Plutus.CIP1694.Test qualified as CIP1694Test
import Plutus.Examples.AccountSimSpec qualified as AccountSimSpec
import Plutus.Examples.DExSpec qualified as DExSpec
import Plutus.Examples.EscrowSpec qualified as EscrowSpec
import Plutus.Examples.GameSpec qualified as GameSpec
import Plutus.Examples.MultiSigSpec qualified as MultiSigSpec
import Plutus.Examples.TemplateSpec qualified as TemplateSpec

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "all tests"
    [ AccountSimSpec.tests
    -- , MultiSigSpec.tests
    -- , DExSpec.tests
    ]
