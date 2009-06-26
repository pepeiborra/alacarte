{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.AlaCarte.Oleg (
    Expr(..), foldExpr, foldExpr',foldExprM, foldExprTop,
    (:+:)(..), (:<:)(..), inject, reinject, match, WithNote(..),
                     ) where
import Control.Applicative
import Control.Monad((>=>),mplus)
import Control.Arrow
import Data.Foldable
import Data.Monoid
import Data.Traversable
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

reinject :: (:<:) f g => Expr f -> Expr g
reinject x = foldExpr (In . inj) x


-- Annotations
-- -----------
-- These are defined here to enable defining a suitable (:<:) instance

newtype WithNote note f a = Note (note, f a) deriving (Show)
instance Functor f  => Functor (WithNote note f)  where fmap f (Note (p, fx))   = Note (p, fmap f fx)
instance Foldable f => Foldable (WithNote note f) where foldMap f (Note (_p,fx)) = foldMap f fx
instance Traversable f => Traversable (WithNote note f) where traverse f (Note (p, fx)) = (Note . (,) p) <$> traverse f fx

instance (IsSub f g HJust, Monoid note) => IsSub f (WithNote note g) HJust where
  ginj = HJust (\x -> case ginj of HJust f -> Note (mempty, f x))
  gprj = HJust (\(Note (_, x)) -> case gprj of HJust prj -> prj x)


-- Solution suggested by Oleg Kiselyov
-- http://wadler.blogspot.com/2008/02/data-types-la-carte.html
-- -----------------------------------------------------------
-- Extended by myself to not require individual Inj HNothing instances
-- and to cope with coproducts in the left hand side.
-- All errors are mine too.


newtype HJust a = HJust a
data HNothing a = HNothing


-- Top level predicate, decomposing the left hand side of the inequality

class (Functor f, Functor g) => (:<:) f g where
  inj :: f a -> g a
  prj :: g a -> Maybe (f a)

instance (IsSub a c HJust, b :<: c) => (:<:) (a :+: b) c where
  inj (Inl x) = case ginj of HJust f -> f x
  inj (Inr x) = inj x
  prj x = (Inl <$> prj1 x) `mplus` (Inr <$> prj x)
   where prj1 = case gprj of HJust f -> f


instance (Functor sub, Functor sup, IsSub sub sup HJust) => (:<:) sub sup where
  inj a = case ginj of HJust f -> f a
  prj a = case gprj of HJust f -> f a

-- We now define predicate, which, given two types f and g, return
-- decides if f :<: g holds -- and if so, yields a witness


class (Functor f, Functor g) => IsSub f g result | f g -> result where
  ginj :: result (f a -> g a)
  gprj :: result (g a -> Maybe (f a))

instance Functor f => IsSub f f HJust where
  ginj = HJust id
  gprj = HJust Just

instance (Functor h, IsSub f g b, IsSub' b f g h result) => IsSub f (g :+: h) result where
  ginj = ginj' (ginj :: b (f a -> g a))
  gprj = gprj' (gprj :: b (g a -> Maybe (f a)))


instance (Functor f, Functor g, h ~ HNothing) => IsSub f g h where
  ginj = HNothing; gprj = HNothing

class IsSub' b f g h result | b f g h -> result where
  ginj' :: b (f a -> g a) -> result (f a -> (g :+: h) a)
  gprj' :: b (g a -> Maybe (f a)) -> result ((g :+: h) a -> Maybe (f a))


instance IsSub' HJust f g h HJust where
  ginj' (HJust pr) = HJust (Inl . pr)
  gprj' (HJust pr) = HJust (\x -> case x of
                                    Inl l -> pr l
                                    Inr _ -> Nothing)

instance (IsSub f h b, IsSub'' b f g h result) => IsSub' HNothing f g h result where
  ginj' _ = ginj'' (ginj :: b (f a -> h a))
  gprj' _ = gprj'' (gprj :: b (h a -> Maybe (f a)))

class IsSub'' b f g h result | b f g h -> result where
  ginj'' :: b (f a -> h a)         -> result (f a -> (g :+: h) a)
  gprj'' :: b (h a -> Maybe (f a)) -> result ((g :+: h) a -> Maybe (f a))

instance IsSub'' HJust f g h HJust where
  ginj'' (HJust tr) = HJust (Inr . tr)
  gprj'' (HJust pr) = HJust (\x -> case x of
                                    Inr r -> pr r
                                    Inl _ -> Nothing)

instance IsSub'' HNothing f g h HNothing where
  ginj'' _ = HNothing
  gprj'' _ = HNothing

{- not ok, but what I want to do

instance (Functor f, Functor g, Functor h, (:<:) f g) => (:<:) f (g :+: 
h) where
inj1 = Inl . inj1

instance (Functor f, Functor g, Functor h, (:<:) f h) => (:<:) f (g :+: 
h) where
inj1 = Inr . inj1

-}

-- need to define the disequalities
-- One may either use Template Haskell for that, or TypeEq from
-- the HList paper
