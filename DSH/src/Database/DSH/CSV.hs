{-# LANGUAGE TemplateHaskell, OverloadedStrings, GADTs, ScopedTypeVariables #-}

module Database.DSH.CSV (csvImport, csvExport, csvExportHandle, csvExportStdout) where

import Database.DSH.Data
import Database.DSH.Impossible

import Text.CSV
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import qualified System.IO as IO
import System.IO (Handle)

csvExport :: (QA a) => FilePath -> [a] -> IO ()
csvExport file as = IO.withFile file IO.WriteMode (\handle -> csvExportHandle handle as)

csvExportStdout :: (QA a) => [a] -> IO ()
csvExportStdout = csvExportHandle IO.stdout

csvExportHandle :: (QA a) => Handle -> [a] -> IO ()
csvExportHandle handle as = T.hPutStr handle csvContent
  where csvContent :: Text
        csvContent = T.unlines (map (toRow . toNorm) as)

        quote :: Text -> Text
        quote s = T.concat ["\"",s,"\""]
        
        escape :: Text -> Text
        escape = (T.replace "\t" "\\t") .
                 (T.replace "\r" "\\r") .
                 (T.replace "\n" "\\n") .
                 (T.replace "\"" "\"\"")

        toRow :: Norm a -> Text
        toRow e = case e of
                    ListN _        -> "Nesting"
                    UnitN          -> quote "()"
                    BoolN b        -> quote (T.pack (show b))
                    CharN c        -> quote (escape (T.singleton c))
                    IntegerN i     -> quote (T.pack (show i))
                    DoubleN d      -> quote (T.pack (show d))
                    TextN t        -> quote (escape t)
                    PairN e1 e2    -> T.concat [toRow e1,",",toRow e2]


csvImport :: (QA a) => FilePath -> Type [a] -> IO (Norm [a])
csvImport = error "csvImport: To be done"
{-
csvImport filepath csvType = do
  let rType = recordType csvType
  contents <- readFile filepath
  let csv1 = case parseCSV filepath contents of
               Left er -> error (show er)
               Right r -> filter (\l -> not (all null l) || length l > 1) (tail r)
  return (ListN (fmap (csvRecordToNorm rType) csv1))
  where csvError :: String -> a
        csvError s = error ("Error in '" ++ filepath ++ "': " ++ s)

        recordType :: QA a => Type [a] -> Type a
        recordType (ListT rType) = rType

        csvRecordToNorm :: QA a => Type a -> [String] -> Norm a
        csvRecordToNorm UnitT  [] = UnitN 
        csvRecordToNorm t      [] = csvError ("When converting record '" ++ show [] ++ "' to a value of type '" ++ show t ++ "'")
        csvRecordToNorm t1     [bs] = csvFieldToNorm t1 bs
        csvRecordToNorm (PairT (t1:: Type b) (t2:: Type c)) (bs : bss) = PairN ((csvFieldToNorm t1 bs):: Norm b) (csvRecordToNorm t2 bss)
        csvRecordToNorm t           rs       = csvError ("When converting record '" ++ show rs ++ "' to a value of type '" ++ show t ++ "'")


        csvFieldToNorm :: QA a => Type a -> String -> Norm a
        csvFieldToNorm t s = case t of
          UnitT      -> UnitN             
          BoolT      -> BoolN    (read s) 
          CharT      -> CharN    (head s) 
          IntegerT   -> IntegerN (read s) 
          DoubleT    -> DoubleN  (read s) 
          TextT      -> TextN    (T.pack s) 
          PairT _ _  -> er
          ListT _    -> er
          ArrowT _ _ -> er
          where er = csvError ("When converting CSV field'" ++ s ++ "' to a value of type '" ++ show t ++ "'")
-}