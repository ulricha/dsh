{-# LANGUAGE GADTs #-}
module Database.DSH.JSON (jsonExport, jsonExportHandle, jsonExportStdout) where

import Database.DSH.Data

import Text.JSON

import qualified Data.Text as Text

import qualified System.IO as IO
import System.IO (Handle)

jsonExport :: (QA a) => FilePath -> [a] -> IO ()
jsonExport file as = IO.withFile file IO.WriteMode (\handle -> jsonExportHandle handle as)

jsonExportStdout :: (QA a) => [a] -> IO ()
jsonExportStdout = jsonExportHandle IO.stdout

jsonExportHandle :: (QA a) => Handle -> [a] -> IO ()
jsonExportHandle handle as = IO.hPutStr handle (encode $ go $ toNorm as)
  
go :: Norm a -> JSValue
go e =  case e of
                  UnitN          -> showJSON "()"
                  BoolN b        -> showJSON b
                  CharN c        -> showJSON c
                  IntegerN i     -> showJSON i
                  DoubleN d      -> showJSON d
                  TextN t        -> showJSON (Text.unpack t)
                  PairN e1 e2    -> JSArray $ go e1 : deTuple e2
                  ListN es       -> JSArray $ map go es

deTuple :: Norm a -> [JSValue]
deTuple (PairN e1 e2) = go e1 : deTuple e2
deTuple n             = [go n]