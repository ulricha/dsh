{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.Redundant where

import Text.Printf
import Debug.Trace

import Control.Monad
import qualified Data.Map as M

import Database.Algebra.Rewrite
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data
  
removeRedundancy :: DagRewrite VL Bool
removeRedundancy = iteratively $ preOrder (return M.empty) redundantRules

redundantRules :: RuleSet VL ()
redundantRules = [ mergeStackedDistDesc 
                 , restrictCombineDBV 
                 , restrictCombinePropLeft 
                 , pullRestrictThroughPair
                 , pairedProjections
                 , binOpSameSource
                 , descriptorFromProject ]

mergeStackedDistDesc :: Rule VL ()
mergeStackedDistDesc q = 
  $(pattern [| q |] "R1 ((valVec1) DistLift (ToDescr (first=R1 ((valVec2) DistLift (ToDescr (foo))))))"
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
  $(pattern [| q |] "R2 (c=CombineVec (qb) (a) (b))"
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
          projectNode <- insertM $ UnOp (ProjectRename (PosCol, Number)) selectNode
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
  
-- FIXME ensure that the union of the columns of both projections is the original input vector
pairedProjections :: Rule VL ()
pairedProjections q = 
  $(pattern [| q |] "(ProjectL ps1 (q1)) PairL (ProjectL ps2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        
        return $ do
          logRewriteM "Redundant.PairedProjections" q
          relinkParentsM q $(v "q1") |])

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
