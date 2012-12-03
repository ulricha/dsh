{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Flattening.Optimizer.VL.Rewrite.DescriptorModifiers where

import           Control.Monad
import           Data.Functor

import Database.DSH.Flattening.Optimizer.Common.Shape
import Database.DSH.Flattening.Optimizer.VL.Properties.IndexSpace
import Database.DSH.Flattening.Optimizer.VL.Properties.Types
import Database.DSH.Flattening.Optimizer.VL.Rewrite.Common

import Database.DSH.Flattening.Optimizer.VL.Properties.AbstractDomains

import           Database.Algebra.Dag.Common
import           Database.Algebra.Rewrite
import           Database.Algebra.VL.Data

stripFromRoot :: VLRewrite Bool
stripFromRoot = iteratively $ preOrder inferBottomUp descriptorNoOps

descriptorNoOps :: VLRuleSet BottomUpProps
descriptorNoOps = [ noOpRenamingProjRename ]
                  -- , noOpRenamingProjAdmin ]
--                  , constantDescriptorChain
--                  , outerMostRootSegment
--                  , outerMostRootPropRename ]

hasConstDesc :: VectorProp ConstVec -> Bool
hasConstDesc (VProp (DBVConst (ConstDescr _) _))      = True
hasConstDesc (VProp (DescrVecConst (ConstDescr _)))   = True
hasConstDesc _                                        = False

-- Walk down a chain of descriptor modifiers and return the first
-- non-descriptor modifier if it is constant. Otherwise, fail the match.
searchConstantDescr :: AlgNode -> Match VL BottomUpProps Shape AlgNode
searchConstantDescr q = do
  op <- getOperator q
  case op of
    BinOp PropRename _ c2 -> searchConstantDescr c2
    UnOp Segment c -> searchConstantDescr c
    _ -> do
      predicate =<< (hasConstDesc . constProp) <$> properties q
      return q

{- Try to find a chain of descriptor-modifying operators (e.g. PropRename, Segment) which
form a noop because the desccriptor is constant at the beginning of the chain and at the end. -}
constantDescriptorChain :: VLRule BottomUpProps
constantDescriptorChain q =
  $(pattern 'q "(_) PropRename (qv)"
    [| do
        predicate =<< (hasConstDesc . constProp) <$> properties q
        chainStart <- searchConstantDescr $(v "qv")

        return $ do
          logRewrite "DescriptorModifiers.ConstantDescriptorChain" q
          op <- operator chainStart
          replace q op |])

-- Remove a Segment operator if the node represents the outermost
-- query. In this case, the descriptor is irrelevant and any operator
-- which just modifies the descriptor can safely be removed.
outerMostRootSegment :: VLRule BottomUpProps
outerMostRootSegment q =
  $(pattern 'q "Segment (q1)"
    [| do
        predicate =<<isOuterMost q <$> lookupExtras

        return $ do
          logRewrite "DescriptorModifiers.OuterMostRootSegment" q
          relinkParents q $(v "q1")
          replaceRootWithShape q $(v "q1") |])

-- Remove a PropRename operator if the node represents the outermost
-- query. In this case, the descriptor is irrelevant and any operator
-- which just modifies the descriptor can safely be removed.
outerMostRootPropRename :: VLRule BottomUpProps
outerMostRootPropRename q =
  $(pattern 'q "(_) PropRename (q1)"
    [| do
        predicate =<< isOuterMost q <$> lookupExtras

        return $ do
          logRewrite "DescriptorModifiers.OuterMostRootPropRename" q
          relinkParents q $(v "q1")
          replaceRootWithShape q $(v "q1") |])

-- FIXME this is a weak version. Use abstract knowledge about index space transformations
-- to establish the no op property.
noOpRenamingProjRename :: VLRule BottomUpProps
noOpRenamingProjRename q =
  $(pattern 'q "(ProjectRename p (_)) PropRename (q1)"
    [| do
        case $(v "p") of
          (STPosCol, STPosCol)     -> return ()
          (STDescrCol, STDescrCol) -> return ()
          _                        -> fail "no match"

        return $ do
          logRewrite "DescriptorModifiers.NoOpRenaming.ProjectRename" q
          replaceRootWithShape q $(v "q1")
          relinkParents q $(v "q1") |])


-- Eliminate a NOOP PropRename operator which updates the descriptor column
-- with the same values it had before.
-- Beware: this rewrite propably interferes with Join removal: the PropRename
-- must be eliminated in a larger context.
noOpRenamingProjAdmin :: VLRule BottomUpProps
noOpRenamingProjAdmin q =
  $(pattern 'q "(DescToRename (ToDescr (qd))) PropRename (ProjectAdmin ps (qv))"
    [| do
         posProj <- case $(v "ps") of
                      (DescrPosCol, posProj) -> return posProj
                      _                      -> fail "no match"

         qdPosDom <- posSpaceDBV <$> indexSpaceProp <$> properties $(v "qd")
         qvPosDom <- posSpaceDBV <$> indexSpaceProp <$> properties $(v "qv")

         -- ensure that the position values on the right side (qv) originate from
         -- the operator which generates the rename vector.
         -- In this case, posold (left) and descr (right, copied from positions)
         -- are aligned.
         -- These properties establish that the PropRename is a noop: It updates the
         -- descriptor column of qv with the same values it had before.
         predicate $ qvPosDom `subDomain` qdPosDom

         return $ do
           logRewrite "DescriptorModifiers.NoOpRenaming.ProjectAdmin" q
           if posProj == PosIdentity
             then relinkParents q $(v "qv")
             else void $ relinkToNew q $ UnOp (ProjectAdmin (DescrIdentity, posProj)) $(v "qv") |])

