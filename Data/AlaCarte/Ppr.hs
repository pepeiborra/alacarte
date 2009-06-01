{-# LANGUAGE TypeOperators #-}
module Data.AlaCarte.Ppr (module Data.AlaCarte, PprF(..), pprExpr) where

import Data.AlaCarte
import Text.PrettyPrint (Doc)

class Functor f => PprF f where pprF :: f Doc -> Doc
instance (PprF f, PprF g) => PprF (f :+: g) where
  pprF (Inl l) = pprF l; pprF (Inr r) = pprF r

pprExpr :: PprF f => Expr f -> Doc
pprExpr = foldExpr pprF