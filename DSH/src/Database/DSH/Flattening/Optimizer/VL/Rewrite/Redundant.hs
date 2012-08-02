{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.Redundant (removeRedundancy) where

import Debug.Trace

import Control.Monad
import qualified Data.Map as M

import Database.Algebra.Rewrite
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data
  
import Optimizer.VL.Rewrite.MergeProjections
import Optimizer.VL.Rewrite.Common
import Optimizer.VL.Properties.Types
import Optimizer.VL.Properties.VectorSchema
  
removeRedundancy :: DagRewrite VL Bool
removeRedundancy = iteratively $ sequenceRewrites [ cleanup
                                                  , preOrder (return M.empty) redundantRules
                                                  , preOrder inferBottomUp redundantRulesWithProperties ]
                   
cleanup :: DagRewrite VL Bool
cleanup = sequenceRewrites [ mergeProjections ]

redundantRules :: RuleSet VL ()
redundantRules = [ mergeStackedDistDesc 
                 , restrictCombineDBV 
                 , restrictCombinePropLeft 
                 , pullRestrictThroughPair
                 , binOpSameSource
                 , descriptorFromProject ]
                 
redundantRulesWithProperties :: RuleSet VL BottomUpProps
redundantRulesWithProperties = [ pairFromSameSource 
                               , pairedProjections
                               , noOpProject
                               , toDescr ]
                 
mergeStackedDistDesc :: Rule VL ()
mergeStackedDistDesc q = 
  $(pattern [| q |] "R1 ((valVec1) DistLift (ToDescr (first=R1 ((valVec2) DistLift (ToDescr (_))))))"
    [| do
        predicate $ $(v "valVec1") == $(v "valVec2")
        return $ do
          logRewriteM "Redundant.MergeStackedDistDesc" q
          relinkParentsM q $(v "first") |])
  
restrictCombineDBV :: Rule VL ()
restrictCombineDBV q =
  $(pattern [| q |] "R1 (CombineVec (qb1) (ToDescr (R1 ((q1) RestrictVec (qb2)))) (ToDescr (R1 ((q2) RestrictVec (NotVec (qb3))))))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        predicate $ $(v "qb1") == $(v "qb2") && $(v "qb1") == $(v "qb3")
        return $ do
          logRewriteM "Redundant.RestrictCombine.DBV" q
          relinkParentsM q $(v "q1") |])

restrictCombinePropLeft :: Rule VL ()
restrictCombinePropLeft q =
  $(pattern [| q |] "R2 (c=CombineVec (qb) (_) (_))"
    [| do
        parentNodes <- parents $(v "c")
        parentOps <- mapM operator parentNodes
        let r1 = filter (\(_, op) -> case op of { UnOp R1 _ -> True; _ -> False }) $ zip parentNodes parentOps
        r1Parents <-
          case r1 of
            [(r1Node, _)] -> liftM length $ parents r1Node
            _ -> fail ""
        predicate $ r1Parents == 0

        return $ do
          logRewriteM "Redundant.RestrictCombine.PropLeft" q
          selectNode <- insertM $ UnOp SelectItem $(v "qb") 
          projectNode <- insertM $ UnOp (ProjectRename (STPosCol, STNumber)) selectNode
          relinkParentsM q projectNode |])
  
pullRestrictThroughPair :: Rule VL ()
pullRestrictThroughPair q =
  $(pattern [| q |] "(R1 ((qp1=ProjectL _ (q1)) RestrictVec (qb1))) PairL (R1 ((qp2=ProjectL _ (q2)) RestrictVec (qb2)))"
    [| do
        predicate $ $(v "qb1") == $(v "qb2")
        predicate $ $(v "q1") == $(v "q2")
        
        return $ do
          logRewriteM "Redundant.PullRestrictThroughPair" q
          pairNode <- insertM $ BinOp PairL $(v "qp1") $(v "qp2")
          restrictNode <- insertM $ BinOp RestrictVec pairNode $(v "qb1")
          r1Node <- insertM $ UnOp R1 restrictNode
          relinkParentsM q r1Node |])
  
binOpSameSource :: Rule VL ()
binOpSameSource q =
  $(pattern [| q |] "(ProjectL ps1 (q1)) VecBinOpL op (ProjectL ps2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        (c1, c2) <- case ($(v "ps1"), $(v "ps2")) of
          ([c1], [c2]) -> return (c1, c2)
          _            -> fail ""

        return $ do
          logRewriteM "Redundant.BinOpSameSource" q
          opNode <- insertM $ UnOp (VecBinOpSingle ($(v "op"), c1, c2)) $(v "q2")
          relinkParentsM q opNode |])
        
descriptorFromProject :: Rule VL ()
descriptorFromProject q =
  $(pattern [| q |] "ToDescr (ProjectL _ (q1))"
    [| do
        return $ do
          logRewriteM "Redundant.DescriptorFromProject" q
          replaceM q $ UnOp ToDescr $(v "q1") |])
  
-- Remove a PairL operator if both inputs are the same and do not have payload columns
pairFromSameSource :: Rule VL BottomUpProps
pairFromSameSource q =
  $(pattern [| q |] "(q1) PairL (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        schema1 <- liftM vectorSchemaProp $ properties $(v "q1")
        schema2 <- liftM vectorSchemaProp $ properties $(v "q2")
        case (schema1, schema2) of
          (VProp (ValueVector i1), VProp (ValueVector i2)) | i1 == i2 && i1 == 0 -> return ()
          (VProp DescrVector, VProp DescrVector)                                 -> return ()
          _                                                                      -> fail "no match"
        return $ do
          logRewriteM "Redundant.PairFromSame" q
          relinkParentsM q $(v "q1") |])
  
-- Remove a ProjectL or ProjectA operator that does not change the vector schema
noOpProject :: Rule VL BottomUpProps
noOpProject q =
  $(pattern [| q |] "[ProjectL | ProjectA] ps (q1)"
    [| do
        schema <- liftM vectorSchemaProp $ properties $(v "q1")
        predicate $ schemaWidth schema == length $(v "ps")
        predicate $ all (uncurry (==)) $ zip ([1..] :: [DBCol]) $(v "ps")
        
        return $ do
          logRewriteM "Redundant.NoOpProject" q
          relinkParentsM q $(v "q1") |])
          
-- Remove a ToDescr operator whose input is already a descriptor vector
toDescr :: Rule VL BottomUpProps
toDescr q =
  $(pattern [| q |] "ToDescr (q1)"
    [| do
        schema <- liftM vectorSchemaProp $ properties $(v "q1")
        case schema of
          VProp DescrVector -> return ()
          _                 -> fail "no match"
        return $ do
          logRewriteM "Redundant.ToDescr" q
          relinkParentsM q $(v "q1") |])

pairedProjections :: Rule VL BottomUpProps
pairedProjections q = 
  $(pattern [| q |] "(ProjectL ps1 (q1)) PairL (ProjectL ps2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (schemaWidth . vectorSchemaProp) $ properties $(v "q1")
        
        return $ do
          if ($(v "ps1") ++ $(v "ps2")) == [1 .. w] 
            then do
              logRewriteM "Redundant.PairedProjections.NoOp" q
              relinkParentsM q $(v "q1")
            else do
              logRewriteM "Redundant.PairedProjections.Reorder" q
              let op = UnOp (ProjectValue (DescrIdentity, PosIdentity, map PLCol $ $(v "ps1") ++ $(v "ps2"))) $(v "q1")
              projectNode <- insertM op
              relinkParentsM q projectNode |])
  
              
