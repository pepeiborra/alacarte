module Data.AlaCarte.Ppr where

import Data.AlaCarte
import Text.PrettyPrint (Doc)

class Functor f => PprF f where pprF :: f Doc -> Doc

pprExpr :: PprF f => Expr f -> Doc
pprExpr = foldExpr pprF