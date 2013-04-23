{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Flattening.Translate.Algebra2Query (generateX100Query, generatePFXML, generateSQL) where

import           Text.PrettyPrint.HughesPJ

import           Text.XML.HaXml                                (children, deep, tag, xmlParse)
import qualified Text.XML.HaXml                                as X

import qualified Data.IntMap                                   as IM
import qualified Data.Map                                      as M
import           Data.Maybe

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Common
import           Database.Algebra.Pathfinder.Data.Algebra
import           Database.Algebra.Pathfinder.Render.XML        hiding (Graph, XML, getNode, node)
import           Database.Algebra.X100.Data
import           Database.Algebra.X100.Render

import           Database.DSH.Flattening.Common.Data.QueryPlan hiding (mkQueryPlan)
import           Database.DSH.Impossible
import           Database.DSH.Flattening.VL.Data.DBVector
import qualified Database.DSH.Flattening.VL.Data.Query         as Ext
import qualified Database.DSH.Flattening.VL.Data.Query         as Q
import           Database.Pathfinder

import           System.IO.Unsafe

generateX100Query :: QueryPlan X100Algebra -> Q.Query Q.X100
generateX100Query x100Plan = convertQuery $ queryShape x100Plan
 where
    m' :: NodeMap X100Algebra
    m' = nodeMap $ queryDag x100Plan

    convertQuery :: TopShape -> Q.Query Q.X100
    convertQuery (PrimVal (DBP r' _) l)     = Q.PrimVal (Q.X100 r' $ generateQuery m' r') $ convertLayout l
    convertQuery (ValueVector (DBV r' _) l) = Q.ValueVector (Q.X100 r' $ generateQuery m' r') $ convertLayout l

    convertLayout :: TopLayout -> Q.Layout Q.X100
    convertLayout (InColumn i)        = Q.InColumn i
    convertLayout (Nest (DBV r' _) l) = Q.Nest (Q.X100 r' $ generateQuery m' r') $ convertLayout l
    convertLayout (Pair p1 p2)        = Q.Pair (convertLayout p1) (convertLayout p2)

generatePFXML :: QueryPlan PFAlgebra -> Q.Query Q.XML
generatePFXML pfPlan = convertQuery $ queryShape pfPlan
    where
        convertQuery :: TopShape -> Q.Query Q.XML
        convertQuery (PrimVal (DBP r' _) l) = Q.PrimVal (Q.XML r' $ toXML' (withItem $ columnsInLayout l) r') $ convertLayout l
        convertQuery (ValueVector (DBV r' _) l) = Q.ValueVector (Q.XML r' $ toXML' (withItem $ columnsInLayout l) r') $ convertLayout l

        convertLayout :: TopLayout -> Q.Layout Q.XML
        convertLayout (InColumn i)        = Q.InColumn i
        convertLayout (Nest (DBV r' _) l) = Q.Nest (Q.XML r' $ toXML' (withItem $ columnsInLayout l) r') $ convertLayout l
        convertLayout (Pair p1 p2)        = Q.Pair (convertLayout p1) (convertLayout p2)

        itemi :: Int -> Element ()
        itemi i = [attr "name" $ "item" ++ show i, attr "new" "false", attr "function" "item", attr "position" (show i)] `attrsOf` xmlElem "column"

        withItem :: Int -> [Element ()]
        withItem i = (iterCol:posCol:[ itemi i' | i' <- [1..i]])

        nodeTable = M.fromList $ IM.toList $ nodeMap $ queryDag pfPlan

        toXML' :: [Element ()] -> AlgNode -> String
        toXML' cs n = render $ document $ mkXMLDocument $ mkPlanBundle $
                        runXML False M.empty IM.empty $
                        mkQueryPlan Nothing (xmlElem "property") $
                        runXML True nodeTable (queryTags pfPlan) $ serializeAlgebra cs n

generateSQL :: Ext.Query Ext.XML -> Ext.Query Ext.SQL
generateSQL (Ext.ValueVector (Ext.XML i r') lyt) = Ext.ValueVector ((\(q, s) -> Ext.SQL i s q) $ translate r') $ translateLayout lyt
generateSQL (Ext.PrimVal (Ext.XML i r') lyt) = Ext.PrimVal ((\(q, s) -> Ext.SQL i s q) $ translate r') $ translateLayout lyt

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
