module Language.ParallelLang.DBPH (nkl2SQL, nkl2Alg, nkl2Vec,nkl2fkl, ReconstructionPlan(..), Query(..), SQL(..), Schema) where

import qualified Language.ParallelLang.NKL.Data.NKL as NKL
import qualified Language.ParallelLang.FKL.Data.FKL as FKL

import Language.ParallelLang.VL.Data.Query
import Language.ParallelLang.FKL.Data.WorkUnits

-- import Language.ParallelLang.Translate.Algebra2SQL
-- import Language.ParallelLang.Translate.Vec2Algebra
import Language.ParallelLang.Translate.TransM (runTransform)
import Language.ParallelLang.Translate.RewritePhases
import Language.ParallelLang.Common.Data.Config (normalCompilation)
import Language.ParallelLang.Translate.NKL2FKL (flatTransform)
-- import Language.ParallelLang.Translate.Detupler (detuple)
-- import Language.ParallelLang.Translate.Vectorise
-- import Language.ParallelLang.VL.Data.VectorTypes

nkl2SQL = undefined
nkl2Alg = undefined
nkl2Vec = undefined
{-
nkl2SQL :: NKL.Expr -> (Query SQL, ReconstructionPlan)
nkl2SQL e = let (e', r) = nkl2Alg e
             in (toSQL e', r)

nkl2Alg :: NKL.Expr -> (Query XML, ReconstructionPlan)
nkl2Alg e = let (e', r) = nkl2Vec' e
             in (toXML $ toAlgebra e', r)
             
nkl2Vec :: NKL.Expr -> String
nkl2Vec e = show $ fst $ nkl2Vec' e
-}
nkl2fkl :: NKL.Expr -> String
nkl2fkl e = show $ runTransform normalCompilation $
             do 
                 e' <- flatTransform e >>= runRWPhase1 -- >>= detuple 
                 r <- runRWPhase2 e'
                 return r
{-
nkl2Vec' :: NKL.Expr -> (FKL.Expr VType, ReconstructionPlan)
nkl2Vec' e = runTransform normalCompilation  $ 
                do 
                 (e', reconstruction) <- flatTransform e >>= runRWPhase1 >>= detuple 
                 r <- runRWPhase2 e' >>= runVectorise 
                 return (r, reconstruction)
-}