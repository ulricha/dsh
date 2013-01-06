module Database.DSH.Flattening.DBPH
  ( nkl2SQL
  , nkl2Alg
  , Query(..)
  , Layout(..)
  , SQL(..)
  , Schema
  , nkl2X100Alg
  , X100(..)
  , nkl2X100File
  , nkl2VLFile
  , nkl2SQLFile
  , nkl2XMLFile
  ) where

import qualified Database.DSH.Flattening.NKL.Data.NKL            as NKL
import qualified Database.DSH.Flattening.NKL.Opt                 as NKLOpt

import           Database.DSH.Flattening.VL.Data.Query

import           Database.DSH.Flattening.Export

import           Database.DSH.Flattening.Common.Data.Type
import           Database.DSH.Flattening.Translate.Algebra2Query
import           Database.DSH.Flattening.Translate.FKL2VL
import           Database.DSH.Flattening.Translate.NKL2FKL       (flatten)
import           Database.DSH.Flattening.Translate.VL2Algebra

(|>) :: a -> (a -> b) -> b
(|>) = flip ($)

nkl2SQL :: NKL.Expr -> (Query SQL, Type)
nkl2SQL e = let (e', t) = nkl2Alg e
            in (generateSQL e', t)

nkl2Alg :: NKL.Expr -> (Query XML, Type)
nkl2Alg e = let q       = NKLOpt.opt e
                          |> flatten
                          |> specializeVectorOps
                          |> implementVectorOpsPF
                          |> generatePFXML
                t       = typeOf e
            in (q, t)

nkl2X100Alg :: NKL.Expr -> (Query X100, Type)
nkl2X100Alg e = let q = NKLOpt.opt e
                        |> flatten
                        |> specializeVectorOps
                        |> implementVectorOpsX100
                        |> generateX100Query
                    t = typeOf e
                in (q, t)

nkl2X100File :: String -> NKL.Expr -> IO ()
nkl2X100File prefix e = NKLOpt.opt e
                        |> flatten
                        |> specializeVectorOps
                        |> implementVectorOpsX100
                        |> (exportX100Plan prefix)

nkl2SQLFile :: String -> NKL.Expr -> IO ()
nkl2SQLFile prefix e = NKLOpt.opt e
                       |> flatten
                       |> specializeVectorOps
                       |> implementVectorOpsPF
                       |> generatePFXML
                       |> generateSQL
                       |> (exportSQL prefix)

nkl2XMLFile :: String -> NKL.Expr -> IO ()
nkl2XMLFile prefix e = NKLOpt.opt e
                       |> flatten
                       |> specializeVectorOps
                       |> implementVectorOpsPF
                       |> generatePFXML
                       |> (exportPFXML prefix)

nkl2VLFile :: String -> NKL.Expr -> IO ()
nkl2VLFile prefix e = NKLOpt.opt e
                      |> flatten
                      |> specializeVectorOps
                      |> exportVLPlan prefix

