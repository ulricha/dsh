{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.PruneEmpty(pruneEmpty) where

import Debug.Trace

import Optimizer.VL.Properties.Types
import Optimizer.VL.Rewrite.Common

import Database.Algebra.Dag.Common
import Database.Algebra.Rewrite
import Database.Algebra.VL.Data

pruneEmpty :: DagRewrite VL Bool
pruneEmpty = postOrder inferBottomUp emptyRules

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
  $(pattern [| q |] "[R1 | R2 | R3] ((q1) Append (q2))"
    [| do
        trace ("left " ++ (show q)) $ predicateM $ (isEmpty $(v "q1")) <&&> (notM $ isEmpty $(v "q2"))
        return $ do
          logRewriteM "Empty.Append.Left" q
          replaceRootM q $(v "q2")
          relinkParentsM q $(v "q2") |])
          
emptyAppendRight :: Rule VL BottomUpProps
emptyAppendRight q =
  $(pattern [| q |] "[R1 | R2 | R3] ((q1) Append (q2))"
    [| do
        o <- operator q
        trace ("match " ++ (show q) ++ " " ++ (show o)) $ predicateM $ (isEmpty $(v "q2")) <&&> (notM $ isEmpty $(v "q1"))
        trace "apply" $ return $ do
          logRewriteM "Empty.Append.Right" q
          replaceRootM q $(v "q1")
          relinkParentsM q $(v "q1") |])
