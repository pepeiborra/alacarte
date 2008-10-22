{-#  OPTIONS_GHC -fglasgow-exts -fallow-overlapping-instances -fallow-undecidable-instances #-}
module Data.AlaCarte (
    Expr(..), foldExpr, foldExpr',foldExprM, foldExprTop,
    WithNote(..), (:+:)(..), (:<:)(..), inject, reinject, match
                     ) where
import Control.Applicative
import Control.Monad((>=>))
import Control.Arrow
import Data.Foldable
import Data.Traversable
import TypePrelude
import TypeEqGeneric1()
import Data.Traversable
import Prelude hiding (mapM)

import Data.AlaCarte.Sums

newtype Expr f = In (f (Expr f))

instance Eq (f (Expr f)) => Eq (Expr f) where In x == In y = x == y

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

newtype WithNote note f a = Note (note, f a) deriving (Show)
instance Functor f  => Functor (WithNote note f)  where fmap f (Note (p, fx))   = Note (p, fmap f fx)
instance Foldable f => Foldable (WithNote note f) where foldMap f (Note (_p,fx)) = foldMap f fx
instance Traversable f => Traversable (WithNote note f) where traverse f (Note (p, fx)) = (Note . (,) p) <$> traverse f fx
instance Eq (f a) => Eq (WithNote note f a) where Note (_, f1) == Note (_, f2) = f1 == f2
instance Ord (f a) => Ord (WithNote note f a) where Note (_, f1) `compare` Note (_, f2) = compare f1 f2

{-      Compatible won't fly.
        The Haskell type checker is no theorem prover
data T
data F
class B x where b :: x -> Bool
instance B T where b = const True
instance B F where b = const False

data E1 a
data E2 a

class B b => Compatible f g b | f g -> b where injectOr :: Expr f -> Expr g -> Expr g -> Expr g
instance b ~ F => Compatible f g b
instance (f :<: g) => Compatible f g T
--instance Compatible E1 E2 T
-}

-- We are going to need two levels actually.
-- First decompose the lhs, and then the rhs

-- We are now going to try a different thing.
-- First, we will flatten each tuple of sums into
-- a plain list. Then we will use standard HList
-- machinery to determine if the union equals to sup
-- (or the intersection to sub, or the difference
-- between sup and the intersection is null).

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

instance (Functor l, Functor r) => TypTree HTrue (l :+: r) (l :+: r) where
  inj1 _ = id
  prj1 _ = Just

instance (g :<: i, Functor f) => TypTree HTrue (f :+: g) (f :+: i) where
  inj1 _ (Inl l) = inj l
  inj1 _ (Inr r) = (Inr $ inj r)
  prj1 _ (Inl l) = Just $ Inl l
  prj1 _ (Inr r) = Inr <$> prj r

instance (f :<: i, Functor g) => TypTree HTrue (f :+: g) (g :+: i) where
  inj1 _ (Inl l) = (Inr $ inj l)
  inj1 _ (Inr r) = inj r
  prj1 _ (Inl l) = Just $ Inr l
  prj1 _ (Inr r) = Inl <$> prj r


-- Transitivity, an impossible dream
--instance (Functor a, a :<: b, b :<: c) => (:<:) a c

{-
instance (Functor f, Functor g) => TypTree f (f :+: g) where
  inj = Inl
  prj (Inl t) = Just t
  prj _       = Nothing
-}
instance (Functor f, Functor g, Functor h, TypTree HTrue f g) =>
  TypTree HTrue f (h :+: g) where
    inj1 _         = Inr . inj1 (proxy::HTrue)
    prj1 _ (Inl t) = Nothing
    prj1 _ (Inr t) = prj1 (proxy::HTrue) t


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
class TypOr b1 b2 res | b1 b2 -> res
instance TypOr HFalse HFalse HFalse
instance TypOr HFalse HTrue  HTrue
instance TypOr HTrue  HFalse HTrue
instance TypOr HTrue  HTrue  HTrue

class IsSum (f :: * -> *) b | f -> b
instance IsSum (a :+: b) HTrue
instance false ~ HFalse => IsSum f false