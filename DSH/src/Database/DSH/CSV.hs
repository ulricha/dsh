module Database.DSH.CSV (csvImport, csvExport, csvExportHandle, csvExportStdout) where

import Database.DSH.Data
import Database.DSH.Impossible

import Text.CSV
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import qualified System.IO as IO
import System.IO (Handle)

csvExport :: (QA a,TA a) => FilePath -> [a] -> IO ()
csvExport file as = IO.withFile file IO.WriteMode (\handle -> csvExportHandle handle as)

csvExportStdout :: (QA a, TA a) => [a] -> IO ()
csvExportStdout = csvExportHandle IO.stdout

csvExportHandle :: (QA a, TA a) => Handle -> [a] -> IO ()
csvExportHandle handle as = T.hPutStr handle csvContent
  where csvContent :: Text
        csvContent = T.unlines (map (toRow . toExp) as)

        quote :: Text -> Text
        quote s = T.concat ["\"",s,"\""]
        
        escape :: Text -> Text
        escape = (T.replace "\t" "\\t") .
                 (T.replace "\r" "\\r") .
                 (T.replace "\n" "\\n") .
                 (T.replace "\"" "\"\"")

        toRow :: Exp a -> Text
        toRow e = case e of
                    ListE _        -> "Nesting"
                    UnitE          -> quote "()"
                    BoolE b        -> quote (T.pack (show b))
                    CharE c        -> quote (escape (T.singleton c))
                    IntegerE i     -> quote (T.pack (show i))
                    DoubleE d      -> quote (T.pack (show d))
                    TextE t        -> quote (escape t)
                    PairE e1 e2    -> T.concat [toRow e1,",",toRow e2]
                    AppE _ _       -> $impossible
                    LamE _         -> $impossible
                    VarE _         -> $impossible
                    TableE _       -> $impossible                    

csvImport :: (Reify (Exp a)) => FilePath -> Type (Exp [Exp a]) -> IO (Exp [Exp a])
csvImport filepath csvType = do
  let rType = recordType csvType
  contents <- readFile filepath
  let csv1 = case parseCSV filepath contents of
               Left er -> error (show er)
               Right r -> filter (\l -> not (all null l) || length l > 1) (tail r)
  return (ListE (fmap (csvRecordToNorm rType) csv1))
  where csvError :: String -> a
        csvError s = error ("Error in '" ++ filepath ++ "': " ++ s)

        recordType :: Type (Exp [Exp a]) -> Type (Exp a)
        recordType (ListT rType) = rType

        csvRecordToNorm :: Type (Exp a) -> [String] -> Exp a
        csvRecordToNorm UnitT  [] = UnitE
        csvRecordToNorm t      [] = csvError ("When converting record '" ++ "[]" ++ "' to a value of type '" ++ show t ++ "'")
        csvRecordToNorm t1     [bs] = csvFieldToNorm t1 bs
        csvRecordToNorm (PairT (t1 :: Type (Exp b)) (t2 :: Type (Exp c))) (bs : bss) = PairE ((csvFieldToNorm t1 bs) :: Exp b) (csvRecordToNorm t2 bss)
        csvRecordToNorm t           rs       = csvError ("When converting record '" ++ show rs ++ "' to a value of type '" ++ show t ++ "'")


        csvFieldToNorm :: Type (Exp a) -> String -> Exp a
        csvFieldToNorm t s = case t of
          UnitT      -> UnitE
          BoolT      -> BoolE    (read s) 
          CharT      -> CharE    (head s) 
          IntegerT   -> IntegerE (read s) 
          DoubleT    -> DoubleE  (read s) 
          TextT      -> TextE    (T.pack s) 
          _          -> er
          where er = csvError ("When converting CSV field'" ++ s ++ "' to a value of type '" ++ show t ++ "'")