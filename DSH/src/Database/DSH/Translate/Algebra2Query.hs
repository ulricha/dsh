{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.Algebra2Query (generateX100Query, generatePFXML) where

import           Text.PrettyPrint.HughesPJ

import qualified Data.IntMap                                   as IM
import qualified Data.Map                                      as M

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Common
import           Database.Algebra.Pathfinder.Data.Algebra
import           Database.Algebra.Pathfinder.Render.XML        hiding (Graph, XML, getNode, node)
import           Database.Algebra.X100.Data
import           Database.Algebra.X100.Render

import           Database.DSH.Common.Data.QueryPlan hiding (mkQueryPlan)
import           Database.DSH.VL.Data.DBVector
import qualified Database.DSH.VL.Data.Query         as Q

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
