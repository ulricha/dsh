module Language.ParallelLang.DBPH (nkl2SQL, nkl2Alg, nkl2fkl, ReconstructionPlan(..), Query(..), SQL(..), Schema, nkl2X100Alg, X100(..)) where

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
             in (toXML $ toPFAlgebra e', t, r)
             

nkl2X100Alg :: NKL.Expr -> (Query X100, Type, ReconstructionPlan)
nkl2X100Alg e = let (e', t, r) = nkl2Vec' e
                in (toX100String $ toX100Algebra e', t, r)

nkl2Vec' :: NKL.Expr -> (FKL.Expr Type, Type, ReconstructionPlan)
nkl2Vec' e = runTransform $ 
                 do 
                  (e', t, reconstruction) <- flatTransform e >>= detuple 
                  return (e', t, reconstruction)

nkl2fkl :: NKL.Expr -> String
nkl2fkl e = show $ runTransform $ liftM (\(x, _, _) -> x) $ flatTransform e >>= detuple 
                 
