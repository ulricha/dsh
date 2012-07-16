{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.PruneEmpty(pruneEmpty) where

import Optimizer.VL.Properties.Types
import Optimizer.VL.Rewrite.Common

import Database.Algebra.Dag.Common
import Database.Algebra.Rewrite
import Database.Algebra.VL.Data

pruneEmpty :: DagRewrite VL Bool
pruneEmpty = preOrder inferBottomUp emptyRules

emptyRules :: RuleSet VL BottomUpProps
emptyRules = [ emptyAppendLeft
             , emptyAppendRight 
             ]
             
isEmpty :: AlgNode -> Match VL BottomUpProps Bool
isEmpty q = do
  ps <- properties q
  return $ emptyProp ps

emptyAppendLeft :: Rule VL BottomUpProps
emptyAppendLeft q =
  $(pattern [| q |] "R1 ((q1) Append (q2))"
    [| do
        predicateM $ (isEmpty $(v "q1")) <&&> (notM $ isEmpty $(v "q2"))
        return $ do
          logRewriteM "Empty.Append.Left" q
          relinkParentsM q $(v "q2") |])
          
emptyAppendRight :: Rule VL BottomUpProps
emptyAppendRight q =
  $(pattern [| q |] "R1 ((q1) Append (q2))"
    [| do
        predicateM $ (isEmpty $(v "q2")) <&&> (notM $ isEmpty $(v "q1"))
        return $ do
          logRewriteM "Empty.Append.Right" q
          relinkParentsM q $(v "q1") |])
          
