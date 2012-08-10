{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.DescriptorModifiers where

import Debug.Trace

import Data.Functor
import Control.Monad

import Optimizer.Common.Match
import Optimizer.Common.Traversal

import Optimizer.Common.Shape
import Optimizer.VL.Properties.Types
import Optimizer.VL.Properties.VectorSchema
import Optimizer.VL.Rewrite.Common

import Database.Algebra.Rewrite
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data
  
stripFromRoot :: VLRewrite Bool
stripFromRoot = iteratively $ preOrder inferBottomUp descriptorNoOps

descriptorNoOps :: VLRuleSet BottomUpProps
descriptorNoOps = [ constantDescriptorChain, noOpRenaming ]
                 
hasConstDesc :: VectorProp ConstVec -> Bool
hasConstDesc (VProp (DBVConst (ConstDescr _) _))      = True
hasConstDesc (VProp (DescrVecConst (ConstDescr _)))   = True
hasConstDesc _                                        = False
                 
-- Walk down a chain of descriptor modifiers and return the first
-- non-descriptor modifier if it is constant. Otherwise, fail the match.
searchConstantDescr :: AlgNode -> OptMatch VL BottomUpProps AlgNode
searchConstantDescr q = do
  op <- getOperator q
  case op of
    BinOp PropRename _ c2 -> searchConstantDescr c2
    UnOp Segment c -> searchConstantDescr c
    _ -> do
      predicate <$> (hasConstDesc . constProp) <$> properties q
      return q
                 
{- Try to find a chain of descriptor-modifying operators (e.g. PropRename, Segment) which
form a noop because the desccriptor is constant at the beginning of the chain and at the end. -}
constantDescriptorChain :: VLRule BottomUpProps
constantDescriptorChain q = 
  $(pattern [| q |] "(_) PropRename (qv)"
    [| do
        predicate <$> (hasConstDesc . constProp) <$> properties q
        chainStart <- searchConstantDescr $(v "qv")
        
        return $ do
          logRewrite "DescriptorModifiers.ConstantDescriptorChain" q
          op <- operator chainStart
          replace q op |])
  
-- FIXME this is a weak version. Use abstract knowledge about index space transformations
-- to establish the no op property.
noOpRenaming :: VLRule BottomUpProps
noOpRenaming q =
  $(pattern [| q |] "(ProjectRename p (_)) PropRename (q1)"
    [| do
        case $(v "p") of
          (STPosCol, STPosCol)     -> return ()
          (STDescrCol, STDescrCol) -> return ()
          _                        -> fail "no match"
          
        return $ do
          logRewrite "DescriptorModifiers.NoOpRenaming" q
          replaceRoot q $(v "q1")
          relinkParents q $(v "q1") |])
          