module Language.ParallelLang.DBPH (nkl2SQL, nkl2Alg, nkl2fkl, ReconstructionPlan(..), Query(..), SQL(..), Schema) where

import qualified Language.ParallelLang.NKL.Data.NKL as NKL
import qualified Language.ParallelLang.FKL.Data.FKL as FKL

import Language.ParallelLang.VL.Data.Query
import Language.ParallelLang.FKL.Data.WorkUnits

import Control.Monad

import Language.ParallelLang.Translate.Algebra2SQL
import Language.ParallelLang.Translate.Vec2Algebra
import Language.ParallelLang.Translate.TransM (runTransform)
import Language.ParallelLang.Translate.NKL2FKL (flatTransform)
import Language.ParallelLang.Translate.Detupler (detuple)
import Language.ParallelLang.Common.Data.Type

nkl2SQL :: NKL.Expr -> (Query SQL, Type, ReconstructionPlan)
nkl2SQL e = let (e', t, r) = nkl2Alg e
             in (toSQL e', t, r)

nkl2Alg :: NKL.Expr -> (Query XML, Type, ReconstructionPlan)
nkl2Alg e = let (e', t, r) = nkl2Vec' e
             in (toXML $ toAlgebra e', t, r)
             
nkl2Vec' :: NKL.Expr -> (FKL.Expr Type, Type, ReconstructionPlan)
nkl2Vec' e = runTransform $ 
                 do 
                  (e', t, reconstruction) <- flatTransform e >>= detuple 
                  return (e', t, reconstruction)

nkl2fkl :: NKL.Expr -> String
nkl2fkl e = show $ runTransform $ liftM (\(x, _, _) -> x) $ flatTransform e >>= detuple 
                 
