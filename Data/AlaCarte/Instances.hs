{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Data.AlaCarte.Instances where

import Control.Applicative
import Data.AlaCarte
import Test.QuickCheck

instance Arbitrary (f(Expr f)) => Arbitrary (Expr f) where
    arbitrary = In <$> arbitrary

instance (Arbitrary (f a), Arbitrary (g a)) => Arbitrary ((f :+: g) a) where
    arbitrary = oneof [Inr <$> arbitrary, Inl <$> arbitrary]
