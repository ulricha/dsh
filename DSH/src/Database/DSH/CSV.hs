{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.CSV (csvImport) where

import Database.DSH.Data
import Database.DSH.Impossible

import Text.CSV
import qualified Data.Text as Text

csvImport :: FilePath -> Type -> IO Norm
csvImport filepath csvType = do
  let rType = recordType csvType
  contents <- readFile filepath
  let csv1 = case parseCSV filepath contents of
               Left er -> error (show er)
               Right r -> filter (\l -> not (all null l) || length l > 1) (tail r)
  return (ListN (fmap (csvRecordToNorm rType) csv1) (ListT rType))

  where

  csvError :: String -> a
  csvError s = error ("Error in '" ++ filepath ++ "': " ++ s)
    
  recordType :: Type -> Type
  recordType (ListT rType) = rType
  recordType _ = $impossible
  
  csvRecordToNorm :: Type -> [String] -> Norm
  csvRecordToNorm t rs = case (t,rs) of
    (UnitT       , []      ) -> UnitN UnitT
    (_           , []      ) -> er
    (t1          , [bs]    ) -> csvFieldToNorm t1 bs
    (TupleT t1 t2, bs : bss) -> TupleN (csvFieldToNorm t1 bs) (csvRecordToNorm t2 bss) (TupleT t1 t2)
    (_           , _       ) -> er
    where
    er = csvError ("When converting record '" ++ show rs ++ "' to a value of type '" ++ show t ++ "'")
    

  csvFieldToNorm :: Type -> String -> Norm
  csvFieldToNorm t s = case t of
    UnitT      -> UnitN             UnitT
    BoolT      -> BoolN    (read s) BoolT
    CharT      -> CharN    (head s) CharT
    IntegerT   -> IntegerN (read s) IntegerT
    DoubleT    -> DoubleN  (read s) DoubleT
    TextT      -> TextN    (Text.pack s) TextT
    TupleT _ _ -> er
    ListT _    -> er
    ArrowT _ _ -> er
    where
    er = csvError ("When converting CSV field'" ++ s ++ "' to a value of type '" ++ show t ++ "'")
