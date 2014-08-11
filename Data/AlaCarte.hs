{-# LANGUAGE TypeOperators, FlexibleContexts, UndecidableInstances #-}
module Data.AlaCarte ( module Data.AlaCarte.CoProducts
                      ,module Data.AlaCarte.Ryan) where

import Data.AlaCarte.Ryan
import Data.AlaCarte.CoProducts

import Control.Applicative
import Control.DeepSeq
import Test.QuickCheck

instance Arbitrary (f(Expr f)) => Arbitrary (Expr f) where
    arbitrary = In <$> arbitrary

instance (Arbitrary (f a), Arbitrary (g a)) => Arbitrary ((f :+: g) a) where
    arbitrary = oneof [Inr <$> arbitrary, Inl <$> arbitrary]


instance NFData (f (Expr f)) => NFData (Expr f) where rnf (In x) = rnf x

instance (NFData (f a), NFData (g a)) => NFData ((f :+: g) a) where
  rnf (Inl l) = rnf l
  rnf (Inr r) = rnf r
