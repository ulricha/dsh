module Language.ParallelLang.DBPH (nkl2SQL, nkl2Alg, nkl2fkl, Query(..), Layout(..), SQL(..), Schema, nkl2X100Alg, X100(..), nkl2X100File, nkl2VLFile, nkl2VLRaw) where

import qualified Language.ParallelLang.NKL.Data.NKL as NKL
import qualified Language.ParallelLang.NKL.Opt as NKLOpt
import qualified Language.ParallelLang.FKL.Data.FKL as FKL

import Language.ParallelLang.VL.Data.Query

import Language.ParallelLang.Translate.Algebra2SQL
import Language.ParallelLang.Translate.FKL2VL
import Language.ParallelLang.Common.TransM (runTransform)
import Language.ParallelLang.Translate.NKL2FKL (flatTransform)
import Language.ParallelLang.Common.Data.Type
import Language.ParallelLang.Translate.VL2Algebra

nkl2SQL :: NKL.Expr -> (Query SQL, Type)
nkl2SQL e = let (e', t) = nkl2Alg e
             in (toSQL e', t)

nkl2Alg :: NKL.Expr -> (Query XML, Type)
nkl2Alg e = let (e', t) = nkl2Vec' e
             in (toXML $ toPFAlgebra $ toVec e', t)
             
nkl2X100Alg :: NKL.Expr -> (Query X100, Type)
nkl2X100Alg e = let (e', t) = nkl2Vec' e
                in (toX100String $ toX100Algebra $ toVec e', t)
                
nkl2X100File :: FilePath -> NKL.Expr -> IO ()
nkl2X100File f e = let (e', _) = nkl2Vec' e
                 in toX100File f $ toX100Algebra $ toVec e'

nkl2Vec' :: NKL.Expr -> (FKL.Expr, Type)
nkl2Vec' e = runTransform $ 
                 do 
                  e' <- flatTransform $ NKLOpt.opt e 
                  let t = typeOf e' 
                  return (e', t)

nkl2fkl :: NKL.Expr -> String
nkl2fkl e = show $ runTransform $ flatTransform e
            
nkl2VLFile :: FilePath -> NKL.Expr -> IO ()
nkl2VLFile f e = let (e', _) = nkl2Vec' e
                 in toVLFile f $ toVec e'
                 
nkl2VLRaw :: NKL.Expr -> String
nkl2VLRaw e = let (e', _) = nkl2Vec' e
               in toVecJSON e'
