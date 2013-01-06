module Database.DSH.Flattening.DBPH (nkl2SQL, nkl2Alg, Query(..), Layout(..), SQL(..), Schema, nkl2X100Alg, X100(..), nkl2X100File, nkl2VLFile) where

import qualified Database.DSH.Flattening.NKL.Data.NKL          as NKL
import qualified Database.DSH.Flattening.NKL.Opt               as NKLOpt

import           Database.DSH.Flattening.VL.Data.Query

import           Database.DSH.Flattening.Export

import           Database.DSH.Flattening.Common.Data.Type
import           Database.DSH.Flattening.Translate.Algebra2SQL
import           Database.DSH.Flattening.Translate.FKL2VL
import           Database.DSH.Flattening.Translate.NKL2FKL     (flatten)
import           Database.DSH.Flattening.Translate.VL2Algebra

nkl2SQL :: NKL.Expr -> (Query SQL, Type)
nkl2SQL e = let (e', t) = nkl2Alg e
             in (toSQL e', t)

nkl2Alg :: NKL.Expr -> (Query XML, Type)
nkl2Alg e = let (e', t) = flatten $ NKLOpt.opt e
             in (generatePathfinderCode $ implementVectorOpsPF $ specializeVectorOps e', t)

nkl2X100Alg :: NKL.Expr -> (Query X100, Type)
nkl2X100Alg e = let (e', t) = flatten $ NKLOpt.opt e
                in (generateX100Code $ implementVectorOpsX100 $ specializeVectorOps e', t)

nkl2X100File :: String -> NKL.Expr -> IO ()
nkl2X100File prefix e = let (e', _) = flatten $ NKLOpt.opt e
                 in exportX100Plan prefix $ implementVectorOpsX100 $ specializeVectorOps e'

nkl2VLFile :: String -> NKL.Expr -> IO ()
nkl2VLFile prefix e = let (e', _) = flatten $ NKLOpt.opt e
                 in exportVLPlan prefix $ specializeVectorOps e'

