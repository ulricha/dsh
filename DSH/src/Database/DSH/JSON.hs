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
  where go :: Norm -> JSValue
        go e =  case e of
                  UnitN _         -> showJSON "()"
                  BoolN b _       -> showJSON b
                  CharN c _       -> showJSON c
                  IntegerN i _    -> showJSON i
                  DoubleN d _     -> showJSON d
                  TextN t _       -> showJSON (Text.unpack t)
                  TupleN e1 e2 _  -> JSArray $ map go (e1 : deTuple e2)
                  ListN es _      -> JSArray $ map go es

deTuple :: Norm -> [Norm]
deTuple (TupleN e1 e2 _) = e1 : deTuple e2
deTuple n = [n]