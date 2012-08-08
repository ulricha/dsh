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
import Optimizer.VL.Rewrite.Expressions
import Optimizer.VL.Properties.Types
import Optimizer.VL.Properties.VectorSchema
  
removeRedundancy :: DagRewrite VL Bool
removeRedundancy = iteratively $ sequenceRewrites [ cleanup
                                                  , preOrder (return M.empty) redundantRules
                                                  , preOrder inferBottomUp redundantRulesWithProperties ]
                   
cleanup :: DagRewrite VL Bool
cleanup = sequenceRewrites [ mergeProjections
                           , optExpressions ]

redundantRules :: RuleSet VL ()
redundantRules = [ mergeStackedDistDesc 
                 , restrictCombineDBV 
                 , restrictCombinePropLeft 
                 , pullRestrictThroughPair
                 , pushRestrictVecThroughProjectL
                 , pushRestrictVecThroughProjectValue
                 , pullPropRenameThroughCompExpr2L
                 , descriptorFromProject ]
                 
redundantRulesWithProperties :: RuleSet VL BottomUpProps
redundantRulesWithProperties = [ pairFromSameSource 
                               , pairedProjections
                               , noOpProject
                               , toDescr ]
                 
mergeStackedDistDesc :: Rule VL ()
mergeStackedDistDesc q = 
  $(pattern [| q |] "R1 ((valVec1) DistLift (d1=ToDescr (first=R1 ((valVec2) DistLift (d2=ToDescr (_))))))"
    [| do
        predicate $ $(v "valVec1") == $(v "valVec2")
        return $ do
          logRewriteM "Redundant.MergeStackedDistDesc" q
          relinkParentsM $(v "d1") $(v "d2")
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

-- Push a RestrictVec through its left input, if this input is a
-- projection operator (ProjectL).
pushRestrictVecThroughProjectL :: Rule VL ()
pushRestrictVecThroughProjectL q =
  $(pattern [| q |] "R1 ((ProjectL p (q1)) RestrictVec (qb))"
    [| do

        return $ do
          logRewriteM "Redundant.PushRestrictVecThroughProjectL" q
          restrictNode <- insertM $ BinOp RestrictVec $(v "q1") $(v "qb")
          r1Node <- insertM $ UnOp R1 restrictNode
          projectNode <- insertM $ UnOp (ProjectL $(v "p")) r1Node
          relinkParentsM q projectNode |])

-- Push a RestrictVec through its left input, if this input is a
-- projection operator (ProjectValue).
pushRestrictVecThroughProjectValue :: Rule VL ()
pushRestrictVecThroughProjectValue q =
  $(pattern [| q |] "R1 ((ProjectValue p (q1)) RestrictVec (qb))"
    [| do
        -- Guard against projections that modify descriptors or positions.
        -- This is to ensure that R2/R3 outputs of the RestrictVec do not 
        -- need to change.
        case $(v "p") of
          (DescrIdentity, PosIdentity, _) -> return ()
          _                               -> fail "no match"
          
        return $ do
          logRewriteM "Redundant.PushRestrictVecThroughProjectValue" q
          restrictNode <- insertM $ BinOp RestrictVec $(v "q1") $(v "qb")
          r1Node <- insertM $ UnOp R1 restrictNode
          projectNode <- insertM $ UnOp (ProjectValue $(v "p")) r1Node
          relinkParentsM q projectNode |])
  
        
descriptorFromProject :: Rule VL ()
descriptorFromProject q =
  $(pattern [| q |] "ToDescr (ProjectL _ (q1))"
    [| do
        return $ do
          logRewriteM "Redundant.DescriptorFromProject" q
          replaceM q $ UnOp ToDescr $(v "q1") |])

-- Pull PropRename operators through a CompExpr2L operator if both
-- inputs of the CompExpr2L operator are renamed according to the same
-- rename vector.

-- This rewrite is sound because CompExpr2L does not care about the
-- descriptor but aligns its inputs based on the positions.
pullPropRenameThroughCompExpr2L :: Rule VL ()
pullPropRenameThroughCompExpr2L q =
  $(pattern [| q |] "((qr1) PropRename (q1)) CompExpr2L e ((qr2) PropRename (q2))"
    [| do
       predicate  $ $(v "qr1") == $(v "qr2")
       
       return $ do
         logRewriteM "Redundant.PullPropRenameThroughCompExpr2L" q
         compNode <- insertM $ BinOp (CompExpr2L $(v "e")) $(v "q1") $(v "q2")
         replaceM q $ BinOp PropRename $(v "qr1") compNode |])
  
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
  
