module Language.ParallelLang.Translate.Algebra2SQL (toSQL) where

import Text.XML.HaXml (Content(..), tag, deep, children, xmlParse, Document(..))

import Language.ParallelLang.VL.Data.Query
import Database.Pathfinder

import System.IO.Unsafe


toSQL :: Query XML -> Query SQL
toSQL r = case r of
            (Tuple rs) -> Tuple $ map toSQL rs
            (DescrVector (XML i r'))     -> DescrVector $ SQL i $ translate r'
            (ValueVector (XML i r'))     -> ValueVector $ SQL i $ translate r'
            (PrimVal (XML i r'))         -> PrimVal     $ SQL i $ translate r'
            (NestedVector (XML i r') rs) -> NestedVector (SQL i $ translate r') $ toSQL rs
            _                            -> error "Should not have happened"
  where
    translate :: String -> String
    translate xml = let r' = unsafePerformIO $ pathfinder xml [] OutputSql
                     in case r' of
                         (Right sql) -> extractSQL sql
                         (Left err) -> error $ "Pathfinder compilation for input: \n"
                                                 ++ xml ++ "\n failed with error: \n"
                                                 ++ err
                                                 
extractSQL :: String -> String
extractSQL xml = let (Document _ _ r _) = xmlParse "query" xml
                  in extractCData $ head $ concatMap children $ (deep $ tag "query") (CElem r undefined)

extractCData :: Content i -> String
extractCData (CString _ d _) = d
extractCData _               = error "Not CDATA"
{-
{-
  Tuple [Query a]
| DescrVector a
| ValueVector a
| PrimVal a
| NestedVector a (Query a)
| PropVector a
| UnEvaluated (Expr T.VType)
-}
-}