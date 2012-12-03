{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.Card(optCard) where

import Debug.Trace

import Control.Monad

import Optimizer.VL.Properties.Types
import Optimizer.VL.Rewrite.Common

import Database.Algebra.Dag.Common
import Database.Algebra.Rewrite
import Database.Algebra.VL.Data

optCard :: DagRewrite VL Bool
optCard = postOrder inferBottomUp cardRules

cardRules :: RuleSet VL BottomUpProps
cardRules = [ distDescCardOneRight ]
            
distDescCardOneRight :: Rule VL BottomUpProps
distDescCardOneRight q =
  $(pattern 'q "R1 ((q1) DistDesc (q2))"
    [| do
        predicateM $ liftM cardOneProp $ properties $(v "q2")
        return $ do
          logRewriteM "Card.One.DistDesc.Right" q
          relinkParentsM q $(v "q1") |])