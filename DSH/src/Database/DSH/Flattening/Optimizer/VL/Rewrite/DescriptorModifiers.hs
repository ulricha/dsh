{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.DescriptorModifiers where

import Debug.Trace

import Control.Monad

import Optimizer.VL.Properties.Types
import Optimizer.VL.Properties.VectorSchema
import Optimizer.VL.Rewrite.Common

import Database.Algebra.Rewrite
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data
  
stripFromRoot :: DagRewrite VL Bool
stripFromRoot = iteratively $ preOrder inferBottomUp descriptorNoOps

descriptorNoOps :: RuleSet VL BottomUpProps
descriptorNoOps = [ constantDescriptorChain ]
                 
hasConstDesc :: VectorProp ConstVec -> Bool
hasConstDesc (VProp (DBVConst (ConstDescr _) _))      = True
hasConstDesc (VProp (DescrVecConst (ConstDescr _)))   = True
hasConstDesc _                                        = False
                 
traverseChain :: AlgNode -> Match VL BottomUpProps AlgNode
traverseChain q = do
  op <- operator q
  case op of
    BinOp PropRename _ c2 -> trace ("at " ++ (show q)) $ traverseChain c2
    UnOp Segment c -> trace ("at " ++ (show q)) $ traverseChain c
    _ -> do
      trace ("at " ++ (show q)) $ predicateM $ liftM (hasConstDesc . constProp) $ properties q
      return q
                 
{- Try to find a chain of descriptor-modifying operators (e.g. PropRename, Segment) which
form a noop because the desccriptor is constant at the beginning of the chain and at the end. -}
constantDescriptorChain :: Rule VL BottomUpProps
constantDescriptorChain q = 
  $(pattern [| q |] "(_) PropRename (qv)"
    [| do
        trace ("top " ++ (show q)) $ predicateM $ liftM (hasConstDesc . constProp) $ properties q
        chainStart <- traverseChain $(v "qv")
        
        trace "match" $ return $ do
          logRewriteM "DescriptorModifiers.ConstantDescriptorChain" q
          op <- operatorM chainStart
          replaceM q op |])
