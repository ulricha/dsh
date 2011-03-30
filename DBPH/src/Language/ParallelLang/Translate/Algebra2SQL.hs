{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.Translate.Algebra2SQL (toSQL) where

import Text.XML.HaXml (Content(..), tag, deep, children, xmlParse, Document(..), AttValue(..))
import qualified Text.XML.HaXml as X

import Data.Maybe
import Language.ParallelLang.VL.Data.Query
import Database.Pathfinder
import Language.ParallelLang.Common.Impossible

import System.IO.Unsafe


toSQL :: Query XML -> Query SQL
toSQL r = case r of
            (TupleVector rs)             -> TupleVector $ map toSQL rs
            (DescrVector (XML i r'))     -> DescrVector $ (\(q, s) -> SQL i s q) $ translate r'
            (ValueVector (XML i r'))     -> ValueVector $ (\(q, s) -> SQL i s q) $ translate r'
            (PrimVal (XML i r'))         -> PrimVal     $ (\(q, s) -> SQL i s q) $ translate r'
            (NestedVector (XML i r') rs) -> NestedVector ((\(q, s) -> SQL i s q) $ translate r') $ toSQL rs
            _                            -> error "Should not have happened"
  where
    translate :: String -> (String, Schema)
    translate xml = let r' = unsafePerformIO $ pathfinder xml [] OutputSql
                     in case r' of
                         (Right sql) -> extractSQL sql
                         (Left err) -> error $ "Pathfinder compilation for input: \n"
                                                 ++ xml ++ "\n failed with error: \n"
                                                 ++ err
                                                 
extractSQL :: String -> (String, Schema)
extractSQL xml = let (Document _ _ r _) = xmlParse "query" xml
                     q = extractCData $ head $ concatMap children $ (deep $ tag "query") (CElem r undefined)
                     s = toSchemeInf $ map process $ concatMap (\x -> deep (tag "column") x) $ deep (tag "schema") (CElem r undefined)
                  in (q, s)


process :: Content i -> (String, Maybe Int)
process (CElem (X.Elem _ attrs _) _) = let name = fromJust $ fmap attrToString $ lookup "name" attrs
                                           pos = fmap attrToInt $ lookup "position" attrs
                                        in (name, pos)
process _ = $impossible

toSchemeInf :: [(String, Maybe Int)] -> Schema
toSchemeInf results = let iterName = fst $ head $ filter (\(_, p) -> isNothing p) results
                          cols = case filter (\(_, p) -> isJust p) results of
                                    []       -> Nothing
                                    [(n, v)] -> Just (n, fromJust v)
                                    _        -> $impossible
                       in (iterName, cols)

extractCData :: Content i -> String
extractCData (CString _ d _) = d
extractCData _               = error "Not CDATA"


attrToInt :: AttValue -> Int
attrToInt (AttValue [(Left i)]) = read i
attrToInt _ = $impossible

attrToString :: AttValue -> String
attrToString (AttValue [(Left i)]) = i
attrToString _ = $impossible
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