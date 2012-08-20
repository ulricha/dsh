{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.Redundant (removeRedundancy) where

import Debug.Trace

import Control.Monad
import qualified Data.Map as M

import Database.Algebra.Rewrite
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data

import Optimizer.Common.Match
import Optimizer.Common.Traversal
  
import Optimizer.VL.Rewrite.MergeProjections
import Optimizer.VL.Rewrite.Common
import Optimizer.VL.Rewrite.Expressions
import Optimizer.VL.Properties.Types
import Optimizer.VL.Properties.VectorType
  
removeRedundancy :: VLRewrite Bool
removeRedundancy = iteratively $ sequenceRewrites [ cleanup
                                                  , preOrder (return M.empty) redundantRules
                                                  , preOrder inferBottomUp redundantRulesWithProperties ]
                   
cleanup :: VLRewrite Bool
cleanup = iteratively $ sequenceRewrites [ mergeProjections
                                         , optExpressions ]

redundantRules :: VLRuleSet ()
redundantRules = [ mergeStackedDistDesc 
                 , restrictCombineDBV 
                 , restrictCombinePropLeft 
                 , pullRestrictThroughPair
                 , pushRestrictVecThroughProjectL
                 , pushRestrictVecThroughProjectPayload
                 , pullPropRenameThroughCompExpr2L
                 , pullPropRenameThroughIntegerToDouble
                 , mergeDescToRenames
                 , descriptorFromProject ]
                 
redundantRulesWithProperties :: VLRuleSet BottomUpProps
redundantRulesWithProperties = [ pairFromSameSource 
                               , pairedProjections
                               , noOpProject
                               , distDescCardOne
                               , toDescr ]
                               
mergeStackedDistDesc :: VLRule ()
mergeStackedDistDesc q = 
  $(pattern [| q |] "R1 ((valVec1) DistLift (d1=ToDescr (first=R1 ((valVec2) DistLift (d2=ToDescr (_))))))"
    [| do
        predicate $ $(v "valVec1") == $(v "valVec2")
        return $ do
          logRewrite "Redundant.MergeStackedDistDesc" q
          relinkParents $(v "d1") $(v "d2")
          relinkParents q $(v "first") |])
  
-- Eliminate the pattern that arises from a filter: Combination of CombineVec, RestrictVec and RestrictVec(Not).
  
restrictCombineDBV :: VLRule ()
restrictCombineDBV q =
  $(pattern [| q |] "R1 (CombineVec (qb1) (ToDescr (R1 ((q1) RestrictVec (qb2)))) (ToDescr (R1 ((q2) RestrictVec (NotVec (qb3))))))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        predicate $ $(v "qb1") == $(v "qb2") && $(v "qb1") == $(v "qb3")
        return $ do
          logRewrite "Redundant.RestrictCombine.DBV" q
          relinkParents q $(v "q1") |])

restrictCombinePropLeft :: VLRule ()
restrictCombinePropLeft q =
  $(pattern [| q |] "R2 (c=CombineVec (qb) (_) (_))"
    [| do
        parentNodes <- getParents $(v "c")
        parentOps <- mapM getOperator parentNodes
        let r1 = filter (\(_, op) -> case op of { UnOp R1 _ -> True; _ -> False }) $ zip parentNodes parentOps
        r1Parents <-
          case r1 of
            [(r1Node, _)] -> liftM length $ getParents r1Node
            _ -> fail ""
        predicate $ r1Parents == 0

        return $ do
          logRewrite "Redundant.RestrictCombine.PropLeft" q
          selectNode <- insert $ UnOp (SelectExpr (Column1 1)) $(v "qb") 
          projectNode <- insert $ UnOp (ProjectRename (STPosCol, STNumber)) selectNode
          relinkParents q projectNode |])
  
pullRestrictThroughPair :: VLRule ()
pullRestrictThroughPair q =
  $(pattern [| q |] "(R1 ((qp1=ProjectL _ (q1)) RestrictVec (qb1))) PairL (R1 ((qp2=ProjectL _ (q2)) RestrictVec (qb2)))"
    [| do
        predicate $ $(v "qb1") == $(v "qb2")
        predicate $ $(v "q1") == $(v "q2")
        
        return $ do
          logRewrite "Redundant.PullRestrictThroughPair" q
          pairNode <- insert $ BinOp PairL $(v "qp1") $(v "qp2")
          restrictNode <- insert $ BinOp RestrictVec pairNode $(v "qb1")
          r1Node <- insert $ UnOp R1 restrictNode
          relinkParents q r1Node |])

-- Push a RestrictVec through its left input, if this input is a
-- projection operator (ProjectL).
pushRestrictVecThroughProjectL :: VLRule ()
pushRestrictVecThroughProjectL q =
  $(pattern [| q |] "R1 ((ProjectL p (q1)) RestrictVec (qb))"
    [| do

        return $ do
          logRewrite "Redundant.PushRestrictVecThroughProjectL" q
          restrictNode <- insert $ BinOp RestrictVec $(v "q1") $(v "qb")
          r1Node <- insert $ UnOp R1 restrictNode
          projectNode <- insert $ UnOp (ProjectL $(v "p")) r1Node
          relinkParents q projectNode |])

-- Push a RestrictVec through its left input, if this input is a
-- projection operator (ProjectValue).
pushRestrictVecThroughProjectPayload :: VLRule ()
pushRestrictVecThroughProjectPayload q =
  $(pattern [| q |] "R1 ((ProjectPayload p (q1)) RestrictVec (qb))"
    [| do
        return $ do
          logRewrite "Redundant.PushRestrictVecThroughProjectValue" q
          restrictNode <- insert $ BinOp RestrictVec $(v "q1") $(v "qb")
          r1Node <- insert $ UnOp R1 restrictNode
          projectNode <- insert $ UnOp (ProjectPayload $(v "p")) r1Node
          relinkParents q projectNode |])
        
descriptorFromProject :: VLRule ()
descriptorFromProject q =
  $(pattern [| q |] "ToDescr (ProjectL _ (q1))"
    [| do
        return $ do
          logRewrite "Redundant.DescriptorFromProject" q
          replace q $ UnOp ToDescr $(v "q1") |])

-- Pull PropRename operators through a CompExpr2L operator if both
-- inputs of the CompExpr2L operator are renamed according to the same
-- rename vector.

-- This rewrite is sound because CompExpr2L does not care about the
-- descriptor but aligns its inputs based on the positions.
pullPropRenameThroughCompExpr2L :: VLRule ()
pullPropRenameThroughCompExpr2L q =
  $(pattern [| q |] "((qr1) PropRename (q1)) CompExpr2L e ((qr2) PropRename (q2))"
    [| do
       predicate  $ $(v "qr1") == $(v "qr2")
       
       return $ do
         logRewrite "Redundant.PullPropRenameThroughCompExpr2L" q
         compNode <- insert $ BinOp (CompExpr2L $(v "e")) $(v "q1") $(v "q2")
         replace q $ BinOp PropRename $(v "qr1") compNode |])
  
-- Pull PropRename operators through a IntegerToDoubleL operator.
pullPropRenameThroughIntegerToDouble :: VLRule ()
pullPropRenameThroughIntegerToDouble q =
  $(pattern [| q |] "IntegerToDoubleL ((qr) PropRename (qv))"
    [| do
        return $ do
          logRewrite "Redundant.PullPropRenameThroughIntegerToDouble" q
          castNode <- insert $ UnOp IntegerToDoubleL $(v "qv")
          replace q $ BinOp PropRename $(v "qr") castNode |])
  
-- Try to merge multiple DescToRename operators which reference the same
-- descriptor vector
mergeDescToRenames :: VLRule ()
mergeDescToRenames q =
  $(pattern [| q |] "DescToRename (d)"
    [| do
        ps <- getParents $(v "d")

        let isDescToRename n = do
              op <- getOperator n
              case op of 
                UnOp DescToRename _ -> return True
                _                   -> return False
       
        redundantNodes <- liftM (filter (/= q)) $ filterM isDescToRename ps
        
        predicate $ not $ null $ redundantNodes
        
        return $ do
          logRewrite "Redundant.MergeDescToRenames" q
          mapM_ (\n -> relinkParents n q) redundantNodes

          -- We have to clean up the graph to remove all now unreferenced DescToRename operators.
          -- If they were not removed, the same rewrite would be executed again, leading to an
          -- infinite loop.
          pruneUnused |])
  
-- Remove a PairL operator if both inputs are the same and do not have payload columns
pairFromSameSource :: VLRule BottomUpProps
pairFromSameSource q =
  $(pattern [| q |] "(q1) PairL (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        vt1 <- liftM vectorTypeProp $ properties $(v "q1")
        vt2 <- liftM vectorTypeProp $ properties $(v "q2")
        case (vt1, vt2) of
          (VProp (ValueVector i1), VProp (ValueVector i2)) | i1 == i2 && i1 == 0 -> return ()
          (VProp DescrVector, VProp DescrVector)                                 -> return ()
          _                                                                      -> fail "no match"
        return $ do
          logRewrite "Redundant.PairFromSame" q
          relinkParents q $(v "q1") |])
  
-- Remove a ProjectL or ProjectA operator that does not change the width
noOpProject :: VLRule BottomUpProps
noOpProject q =
  $(pattern [| q |] "[ProjectL | ProjectA] ps (q1)"
    [| do
        vt <- liftM vectorTypeProp $ properties $(v "q1")
        predicate $ vectorWidth vt == length $(v "ps")
        predicate $ all (uncurry (==)) $ zip ([1..] :: [DBCol]) $(v "ps")
        
        return $ do
          logRewrite "Redundant.NoOpProject" q
          relinkParents q $(v "q1") |])
          
-- Remove a ToDescr operator whose input is already a descriptor vector
toDescr :: VLRule BottomUpProps
toDescr q =
  $(pattern [| q |] "ToDescr (q1)"
    [| do
        vt <- liftM vectorTypeProp $ properties $(v "q1")
        case vt of
          VProp DescrVector -> return ()
          _                 -> fail "no match"
        return $ do
          logRewrite "Redundant.ToDescr" q
          relinkParents q $(v "q1") |])

pairedProjections :: VLRule BottomUpProps
pairedProjections q = 
  $(pattern [| q |] "(ProjectL ps1 (q1)) PairL (ProjectL ps2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        
        return $ do
          if ($(v "ps1") ++ $(v "ps2")) == [1 .. w] 
            then do
              logRewrite "Redundant.PairedProjections.NoOp" q
              relinkParents q $(v "q1")
            else do
              logRewrite "Redundant.PairedProjections.Reorder" q
              let op = UnOp (ProjectPayload $ map PLCol $ $(v "ps1") ++ $(v "ps2")) $(v "q1")
              projectNode <- insert op
              relinkParents q projectNode |])

-- If we encounter a DistDesc which distributes a vector of size one
-- over a descriptor (that is, the cardinality of the descriptor
-- vector does not change), replace the DistDesc by a projection which
-- just adds the (constant) values from the value vector
distDescCardOne :: VLRule BottomUpProps
distDescCardOne q =
  $(pattern [| q |] "R1 ((qc) DistDesc (ToDescr (qv)))"
    [| do
        qvProps <- properties $(v "qc")
        predicate $ case card1Prop qvProps of
                      VProp c -> c
                      _       -> error "distDescCardOne: no single property"
       
        let constVal (ConstPL v) = return $ PLConst v
            constVal _           = fail "no match"
       
        
        constProjs <- case constProp qvProps of
          VProp (DBVConst _ cols) -> mapM constVal cols
          _                       -> fail "no match"
          
        return $ do
          logRewrite "distDescCardOne" q
          projNode <- insert $ UnOp (ProjectPayload constProjs) $(v "qv")
          replace q $ UnOp Segment projNode |])
  
