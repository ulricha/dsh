module Ferry.Internals.Projections where

import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.Extension
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty
    
type Size = Int
type Index = Int

baseMod = "Ferry"

projF :: Size -> Index -> Exp -> Exp
projF s i = app (proj s i)

proj :: Size -> Index -> Exp
proj s i = var . name $ baseMod ++ ".proj_" ++ show s ++ "_" ++ show i

tupleF :: [Exp] -> Exp
tupleF xs = foldl app constr xs
    where
      size = length xs
      constr = var . name $ baseMod ++ ".tuple_" ++ show size