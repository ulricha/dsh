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
emptyRules = [ emptyAppendLeftR1
             , emptyAppendLeftR3
             , emptyAppendRightR1
             , emptyAppendRightR2
             ]
             
isEmpty :: AlgNode -> Match VL BottomUpProps Bool
isEmpty q = do
  ps <- properties q
  return $ emptyProp ps

{- If the left input is empty and the other is not, the resulting value vector
is simply the right input. -}
emptyAppendLeftR1 :: Rule VL BottomUpProps
emptyAppendLeftR1 q =
  $(pattern [| q |] "R1 ((q1) Append (q2))"
    [| do
        predicateM $ (isEmpty $(v "q1")) <&&> (notM $ isEmpty $(v "q2"))
        return $ do
          logRewriteM "Empty.Append.Left.R1" q
          replaceRootM q $(v "q2")
          relinkParentsM q $(v "q2") |])
  
{- If the left input is empty, a propagation vector for the right side
needs to be generated nevertheless. However, since no input comes from
the right side, the propagation vector is simply a NOOP because it
maps pos (posold) to pos (posnew). -}
emptyAppendLeftR3 :: Rule VL BottomUpProps
emptyAppendLeftR3 q =
  $(pattern [| q |] "R3 ((q1) Append (q2))"
    [| do
        predicateM $ (isEmpty $(v "q1")) <&&> (notM $ isEmpty $(v "q2"))
        return $ do
          logRewriteM "Empty.Append.Left.R3" q
          replaceM q $ UnOp (ProjectRename (PosCol, PosCol)) $(v "q2") |])
          
emptyAppendRightR1 :: Rule VL BottomUpProps
emptyAppendRightR1 q =
  $(pattern [| q |] "R1 ((q1) Append (q2))"
    [| do
        predicateM $ (isEmpty $(v "q2")) <&&> (notM $ isEmpty $(v "q1"))
        return $ do
          logRewriteM "Empty.Append.Right.R1" q
          replaceRootM q $(v "q1")
          relinkParentsM q $(v "q1") |])

emptyAppendRightR2 :: Rule VL BottomUpProps
emptyAppendRightR2 q =
  $(pattern [| q |] "R2 ((q1) Append (q2))"
    [| do
        predicateM $ (isEmpty $(v "q2")) <&&> (notM $ isEmpty $(v "q1"))
        return $ do
          logRewriteM "Empty.Append.Right.R2" q
          replaceM q $ UnOp (ProjectRename (PosCol, PosCol)) $(v "q1") |])
