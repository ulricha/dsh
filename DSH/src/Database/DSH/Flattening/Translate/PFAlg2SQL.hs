{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.Flattening.Translate.PFAlg2SQL (toSQL) where

import           Text.XML.HaXml                            (AttValue(..), Content(..), Document(..), children, deep, tag,
 xmlParse)
import qualified Text.XML.HaXml                            as X

import           Data.Maybe
import           Database.DSH.Flattening.Common.Impossible
import qualified Database.DSH.Flattening.VL.Data.Query     as Ext
import           Database.Pathfinder

import           System.IO.Unsafe

toSQL :: Ext.Query Ext.XML -> Ext.Query Ext.SQL
toSQL (Ext.ValueVector (Ext.XML i r') lyt) = Ext.ValueVector ((\(q, s) -> Ext.SQL i s q) $ translate r') $ translateLayout lyt
toSQL (Ext.PrimVal (Ext.XML i r') lyt) = Ext.PrimVal ((\(q, s) -> Ext.SQL i s q) $ translate r') $ translateLayout lyt

translateLayout :: Ext.Layout Ext.XML -> Ext.Layout Ext.SQL
translateLayout (Ext.InColumn i) = Ext.InColumn i
translateLayout (Ext.Nest (Ext.XML i r') lyt) = Ext.Nest ((\(q,s) -> Ext.SQL i s q) $ translate r') (translateLayout lyt)
translateLayout (Ext.Pair l1 l2) = Ext.Pair (translateLayout l1) (translateLayout l2)

translate :: String -> (String, Ext.Schema)
translate xml = let r' = unsafePerformIO $ pathfinder xml "" OutputSql
                 in case r' of
                     (Right sql) -> extractSQL sql
                     (Left err) -> error $ "Pathfinder compilation for input: \n"
                                             ++ xml ++ "\n failed with error: \n"
                                             ++ err

extractSQL :: String -> (String, Ext.Schema)
extractSQL xml = let (Document _ _ r _) = xmlParse "query" xml
                     q = extractCData $ head $ concatMap children $ (deep $ tag "query") (CElem r undefined)
                     s = toSchemeInf $ map process $ concatMap (\x -> deep (tag "column") x) $ deep (tag "schema") (CElem r undefined)
                  in (q, s)


process :: Content i -> (String, Maybe Int)
process (CElem (X.Elem _ attrs _) _) = let name = fromJust $ fmap attrToString $ lookup (X.N "name") attrs
                                           pos = fmap attrToInt $ lookup (X.N "position") attrs
                                        in (name, pos)
process _ = $impossible

toSchemeInf :: [(String, Maybe Int)] -> Ext.Schema
toSchemeInf results = let iterName = fst $ head $ filter (\(_, p) -> isNothing p) results
                          cols = map (\(n, v) -> (n, fromJust v)) $ filter (\(_, p) -> isJust p) results
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
