{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.AlaCarte.Sums where

import Control.Applicative
import Data.Foldable
import Data.Traversable


infixr 6 :+:

data (f :+: g) e = Inl (f e) | Inr (g e)

instance (Eq (f a), Eq (g a)) => Eq ((f :+: g) a) where
    Inl x == Inl y = x == y
    Inr x == Inr y = x == y
    _     == _     = False

-- TODO derive Ord,Enum,and so on.., instances

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl e1)  = Inl (fmap f e1)
  fmap f (Inr e2)  = Inr (fmap f e2)

instance (Foldable f, Foldable g) => Foldable (f :+: g) where
    foldMap f (Inl x) = foldMap f x
    foldMap f (Inr x) = foldMap f x

instance (Traversable f, Traversable g) => Traversable (f :+: g) where
    traverse f (Inl e1) = Inl <$> traverse f e1
    traverse f (Inr e1) = Inr <$> traverse f e1
