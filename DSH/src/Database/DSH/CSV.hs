{-# LANGUAGE ScopedTypeVariables, GADTs #-}
module Database.DSH.CSV (csvImport) where

import Database.DSH.Internals

import qualified Data.Text as T
import Text.CSV

csvImport :: (Reify a) => FilePath -> Type [a] -> IO (Exp [a])
csvImport filepath csvType = do
  let rType = recordType csvType
  contents <- readFile filepath
  let csv1 = case parseCSV filepath contents of
               Left er -> error (show er)
               Right r -> filter (\l -> not (all null l) || length l > 1) (tail r)
  return (ListE (fmap (csvRecordToNorm rType) csv1))
  where csvError :: String -> a
        csvError s = error ("Error in '" ++ filepath ++ "': " ++ s)

        recordType :: Type [a] -> Type a
        recordType (ListT rType) = rType

        csvRecordToNorm :: Type a -> [String] -> Exp a
        csvRecordToNorm UnitT  [] = UnitE
        csvRecordToNorm t      [] = csvError ("When converting record '" ++ "[]" ++ "' to a value of type '" ++ show t ++ "'")
        csvRecordToNorm t1     [bs] = csvFieldToNorm t1 bs
        csvRecordToNorm (PairT (t1 :: Type b) (t2 :: Type c)) (bs : bss) = PairE (csvFieldToNorm t1 bs :: Exp b) (csvRecordToNorm t2 bss)
        csvRecordToNorm t           rs       = csvError ("When converting record '" ++ show rs ++ "' to a value of type '" ++ show t ++ "'")


        csvFieldToNorm :: Type a -> String -> Exp a
        csvFieldToNorm t s = case t of
          UnitT      -> UnitE
          BoolT      -> BoolE    (read s)
          CharT      -> CharE    (head s)
          IntegerT   -> IntegerE (read s)
          DoubleT    -> DoubleE  (read s)
          TextT      -> TextE    (T.pack s)
          _          -> er
          where er = csvError ("When converting CSV field'" ++ s ++ "' to a value of type '" ++ show t ++ "'")