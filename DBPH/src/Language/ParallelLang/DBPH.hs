module Language.ParallelLang.DBPH (nkl2SQL, nkl2Alg, nkl2fkl, Query(..), Layout(..), SQL(..), Schema, nkl2X100Alg, X100(..), nkl2X100File) where

import qualified Language.ParallelLang.NKL.Data.NKL as NKL
import qualified Language.ParallelLang.FKL.Data.FKL as FKL

import Language.ParallelLang.VL.Data.Vector

import Language.ParallelLang.Translate.Algebra2SQL
import Language.ParallelLang.Translate.Vec2Algebra
import Language.ParallelLang.Common.TransM (runTransform)
import Language.ParallelLang.Translate.NKL2FKL (flatTransform)
import Language.ParallelLang.Common.Data.Type

nkl2SQL :: NKL.Expr -> (Query SQL, Type)
nkl2SQL e = let (e', t) = nkl2Alg e
             in (toSQL e', t)

nkl2Alg :: NKL.Expr -> (Query XML, Type)
nkl2Alg e = let (e', t) = nkl2Vec' e
             in (toXML $ toPFAlgebra e', t)
             
nkl2X100Alg :: NKL.Expr -> (Query X100, Type)
nkl2X100Alg e = let (e', t) = nkl2Vec' e
                in (toX100String $ toX100Algebra e', t)
                
nkl2X100File :: FilePath -> NKL.Expr -> IO ()
nkl2X100File f e = let (e', _) = nkl2Vec' e
                 in toX100File f $ toX100Algebra e'

nkl2Vec' :: NKL.Expr -> (FKL.Expr, Type)
nkl2Vec' e = runTransform $ 
                 do 
                  e' <- flatTransform e 
                  let t = typeOf e' 
                  return (e', t)

nkl2fkl :: NKL.Expr -> String
nkl2fkl e = show $ runTransform $ flatTransform e
                 
