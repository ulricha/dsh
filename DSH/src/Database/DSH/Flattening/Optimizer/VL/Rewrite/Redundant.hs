{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.Redundant where

import qualified Data.Map as M

import Database.Algebra.Rewrite
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data
  
removeRedundancy :: DagRewrite VL Bool
removeRedundancy = preOrder (return M.empty) redundantRules

redundantRules :: RuleSet VL ()
redundantRules = [ mergeStackedDistDesc 
                 , restrictCombine ]

mergeStackedDistDesc :: Rule VL ()
mergeStackedDistDesc q = 
  $(pattern [| q |] "R1 ((valVec1) DistLift (ToDescr (first=R1 ((valVec2) DistLift (ToDescr (foo))))))"
    [| do
        predicate $ $(v "valVec1") == $(v "valVec2")
        return $ do
          logRewriteM "Redundant.MergeStackedDistDesc" q
          relinkParentsM q $(v "first") |])
  
restrictCombine :: Rule VL ()
restrictCombine q =
  $(pattern [| q |] "R1 (CombineVec (qb1) (ToDescr (R1 ((q1) RestrictVec (qb2)))) (ToDescr (R1 ((q2) RestrictVec (NotVec (qb3))))))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        predicate $ $(v "qb1") == $(v "qb2") && $(v "qb1") == $(v "qb3")
        return $ do
          logRewriteM "Redundant.RestrictCombine" q
          relinkParentsM q $(v "q1") |])
