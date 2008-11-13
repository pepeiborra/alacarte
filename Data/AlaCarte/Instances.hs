{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Data.AlaCarte.Instances where

import Control.Applicative
import Control.Parallel.Strategies
import Data.AlaCarte
import Test.QuickCheck

instance Arbitrary (f(Expr f)) => Arbitrary (Expr f) where
    arbitrary = In <$> arbitrary

instance (Arbitrary (f a), Arbitrary (g a)) => Arbitrary ((f :+: g) a) where
    arbitrary = oneof [Inr <$> arbitrary, Inl <$> arbitrary]


instance NFData (f (Expr f)) => NFData (Expr f) where rnf (In x) = rnf x

instance (NFData (f a), NFData (g a)) => NFData ((f :+: g) a) where
  rnf (Inl l) = rnf l
  rnf (Inr r) = rnf r
