{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE KindSignatures, TypeOperators #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Data.AlaCarte.Ryan (
    Expr(..), foldExpr, foldExpr',foldExprM, foldExprTop,
    (:+:)(..), (:<:)(..), inject, reinject, reinjectMaybe, match, WithNote(..),
                     ) where
import Control.Applicative
import Control.Monad((>=>), mplus)
import Control.Arrow
import Data.Foldable
import Data.Monoid
import Data.Traversable
import Data.Typeable
import Prelude hiding (mapM)

import Data.AlaCarte.CoProducts

newtype Expr f = In (f (Expr f))

instance Eq (f (Expr f)) => Eq (Expr f) where In x == In y = x == y
instance Ord (f(Expr f)) => Ord (Expr f) where compare (In x) (In y) = compare x y

-- | Bottom traversal
foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In t) = f (fmap (foldExpr f) t)

-- | Bottom traversal, monadic
foldExprM :: (Monad m, Traversable f) => (f a -> m a) -> Expr f -> m a
foldExprM f (In t) = f =<< mapM (foldExprM f) t

-- | Bottom traversal with visibility of the original value
foldExpr' :: Functor f => (Expr f -> f a -> a) -> Expr f -> a
foldExpr' f e@(In t) = f e (foldExpr' f `fmap` t)

-- | Top traversal
foldExprTop :: Functor f => (f (Expr f) -> f(Expr f)) -> Expr f -> Expr f
foldExprTop f (In t) = In (foldExprTop f `fmap` (f t))

inject :: (g :<: f) => g (Expr f) -> Expr f
inject = In . inj

match :: (g :<: f) => Expr f -> Maybe (g (Expr f))
match (In t) = prj t

reinject :: (f :<: g) => Expr f -> Expr g
reinject = foldExpr inject


-- | 'reinject' with failure.
--   Useful if you want to obtain a 'Expr r' from a 'Expr (l :+: r)'
reinjectMaybe :: (g :<: f, Traversable f) => Expr f -> Maybe (Expr g)
reinjectMaybe = foldExprM (fmap In . prj)

-- Subsumption encoding provided by Ryan Ingram in
--  http://www.haskell.org/pipermail/haskell-cafe/2008-February/040098.html
-- and mutilated by myself.

class (Functor sub, Functor sup) => (:<:) sub sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)


instance Functor f => (:<:) f f where
  inj = id
  prj = Just

instance (IsSum f isSum, Functor g, TypTree isSum f g) => (:<:) f g where
  inj = inj1 (proxy::isSum)
  prj = prj1 (proxy::isSum)

instance (Functor f, Functor g) => (:<:) f (f :+: g) where
  inj = Inl
  prj (Inl a) = Just a
  prj _       = Nothing

class (Functor sub, Functor sup) => TypTree isSumSub sub sup where
  inj1 :: isSumSub -> sub a -> sup a
  prj1 :: isSumSub -> sup a -> Maybe (sub a)

-- Transitivity, an impossible dream
--instance (Functor a, a :<: b, b :<: c) => (:<:) a c

{-
instance (Functor f, Functor g) => TypTree f (f :+: g) where
  inj = Inl
  prj (Inl t) = Just t
  prj _       = Nothing
-}


instance (a :<: c, (:<:) b c) => TypTree HTrue (a :+: b) c where
  inj1 _ (Inl x) = inj x
  inj1 _ (Inr x) = inj x
  prj1 _ x = (Inl <$> prj x) `mplus` (Inr <$> prj x)
{-
instance (Functor f, Functor g, Functor h, TypTree HTrue f g) =>
  TypTree HTrue f (h :+: g) where
    inj1 _         = Inr . inj1 (proxy::HTrue)
    prj1 _ (Inl t) = Nothing
    prj1 _ (Inr t) = prj1 (proxy::HTrue) t
-}

-- TypTree.  This is basically the same as (:<:) in the paper.

--
-- The magic all happens here
-- We use "IsTreeMember" to determine if a type is part of a tree with leaves
-- of various types and internal nodes of type (l :+: r).
--
class IsTreeMember (sub :: * -> *) (sup :: * -> *) b | sub sup -> b

instance TypeEq2 x y b => IsTreeMember x y b
instance (IsTreeMember x l bl, IsTreeMember x r br, TypOr bl br b) => IsTreeMember x (l :+: r) b

class (Functor sub, Functor l, Functor r) => TypTree' b sub l r where
    treeInj' :: b -> sub a -> (l :+: r) a
    treePrj' :: b -> (l :+: r) a -> Maybe (sub a)

--
-- We can then use this result to decide whether to select from the left or the right.
--
instance (x :<: l, Functor r) => TypTree' HTrue x l r where
    treeInj' _ = Inl . inj
    treePrj' _ (Inl t) = prj t
    treePrj' _ _       = Nothing
instance (x :<: r, Functor l) => TypTree' HFalse x l r where
    treeInj' _ = Inr . inj
    treePrj' _ (Inr t) = prj t
    treePrj' _ _       = Nothing

--
-- Finally, this allows us to select which treeInj' to use based on the
-- type passed in.
-- 
instance (IsTreeMember x l b, TypTree' b x l r) => TypTree HFalse x (l :+: r) where
    inj1 _ = treeInj' (undefined :: b)
    prj1 _ = treePrj' (undefined :: b)

{-
-- Transitivity. Makes GHC loop !
instance forall sub b sup .  (sub :<: b, b :<: sup) => TypTree HFalse sub sup where
    inj1 _ = ((inj :: b a -> sup a) . inj)
    prj1 s = (prj :: sup a -> Maybe (b a)) >=> prj
-}
----------------------------------------------


-- Annotations
-- -----------
-- These are defined here to enable defining a suitable (:<:) instance

newtype WithNote note f a = Note (note, f a) deriving (Show)
instance Functor f  => Functor (WithNote note f)  where fmap f (Note (p, fx))   = Note (p, fmap f fx)
instance Foldable f => Foldable (WithNote note f) where foldMap f (Note (_p,fx)) = foldMap f fx
instance Traversable f => Traversable (WithNote note f) where traverse f (Note (p, fx)) = (Note . (,) p) <$> traverse f fx

{-
instance (f :<: g, Monoid note) => (:<:) f (WithNote note g) where
    inj x = Note (mempty, inj x)
    prj (Note (_, x)) = prj x
-}

instance (f :<: g, Monoid note) => TypTree HFalse f (WithNote note g) where
  inj1 _ x = Note (mempty, inj x)
  prj1 _ (Note (_, x)) = prj x

-- -----------------
-- Type level
-- -----------------
proxy :: a
proxy = undefined

data HTrue
data HFalse
class HBool x; instance HBool HTrue; instance HBool HFalse

class HBool b => TypeEq x y b | x y -> b
class HBool b => TypeEq2 (x :: * -> *) (y :: * -> *) b | x y -> b
class HBool b => TypeEq3 (x :: (* -> *) -> *) (y :: (* -> *) -> *) b | x y -> b

instance TypeEq  x x HTrue
instance TypeEq2 x x HTrue
instance TypeEq3 x x HTrue

instance (b ~ HFalse) => TypeEq  x y b
instance (b ~ HFalse) => TypeEq2 x y b
instance (b ~ HFalse) => TypeEq3 x y b

class TypOr b1 b2 res | b1 b2 -> res
instance TypOr HFalse HFalse HFalse
instance TypOr HFalse HTrue  HTrue
instance TypOr HTrue  HFalse HTrue
instance TypOr HTrue  HTrue  HTrue

class IsSum (f :: * -> *) b | f -> b
instance IsSum (a :+: b) HTrue
instance false ~ HFalse => IsSum f false
