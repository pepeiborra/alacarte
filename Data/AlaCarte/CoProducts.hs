{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}


module Data.AlaCarte.CoProducts where

import Control.Applicative
import Data.Foldable
import Data.Traversable
import Data.Typeable

infixr 6 :+:

data (f :+: g) e = Inl (f e) | Inr (g e) deriving (Eq, Ord)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl e1)  = Inl (fmap f e1)
  fmap f (Inr e2)  = Inr (fmap f e2)

instance (Foldable f, Foldable g) => Foldable (f :+: g) where
    foldMap f (Inl x) = foldMap f x
    foldMap f (Inr x) = foldMap f x

instance (Traversable f, Traversable g) => Traversable (f :+: g) where
    traverse f (Inl e1) = Inl <$> traverse f e1
    traverse f (Inr e1) = Inr <$> traverse f e1


class Subst (g :: * -> *) (f1 :: * -> *) (f2 :: * -> *) (h :: * -> *) | g f1 f2 -> h
instance Subst f1 f1 f2 f2
instance Subst (f1 :+: f) f1 f2 (f2 :+: f)
instance Subst g f1 f2 g2 => Subst (f :+: g) f1 f2 (f :+: g2)

class Typeable311 (a :: (* -> *) -> (* -> *) -> * -> *) where typeOf311 :: a f g x -> TypeRep
instance Typeable311 (:+:) where
  typeOf311 _ = mkTyConApp (mkTyCon ":+:") []

class Typeable21 (t :: (* -> *) -> * -> *) where typeOf21 :: t f a -> TypeRep
instance (Typeable311 t, Typeable1 f) => Typeable21 (t f) where
  typeOf21 x = typeOf311 x `mkAppTy` typeOf1 (undefined :: f x)

instance (Typeable21 t, Typeable1 f) => Typeable1 (t f) where
  typeOf1 x = typeOf21 x `mkAppTy` typeOf1 (undefined :: f x)

class Typeable11 (t :: (* -> *) -> *) where typeOf11 :: t f -> TypeRep
instance (Typeable11 t, Typeable1 f) => Typeable (t f) where
  typeOf x = typeOf11 x `mkAppTy` typeOf1 (undefined :: f x)