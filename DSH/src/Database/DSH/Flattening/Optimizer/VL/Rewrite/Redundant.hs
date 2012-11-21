{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.Redundant (removeRedundancy, descriptorFromProject) where

import           Control.Applicative
import           Control.Monad
import qualified Data.Map as M
import           Debug.Trace

import           Database.Algebra.Rewrite
import           Database.Algebra.Dag.Common
import           Database.Algebra.VL.Data

import           Optimizer.VL.Properties.AbstractDomains
import           Optimizer.VL.Properties.Types
import           Optimizer.VL.Properties.VectorType
import           Optimizer.VL.Rewrite.Common
import           Optimizer.VL.Rewrite.Expressions
import           Optimizer.VL.Rewrite.MergeProjections
  
removeRedundancy :: VLRewrite Bool
removeRedundancy = iteratively $ sequenceRewrites [ cleanup
                                                  , preOrder (return M.empty) redundantRules
                                                  , preOrder inferBottomUp redundantRulesBottomUp
                                                  , preOrder inferTopDown redundantRulesTopDown ]
                   
cleanup :: VLRewrite Bool
cleanup = iteratively $ sequenceRewrites [ mergeProjections
                                         , optExpressions ]

redundantRules :: VLRuleSet ()
redundantRules = [ restrictCombineDBV 
                 , restrictCombinePropLeft
                 , cleanupSelect
                 , introduceSelectExpr
                 , pullRestrictThroughPair
                 , pushRestrictVecThroughProjectL
                 , pushRestrictVecThroughProjectPayload
                 , pullPropRenameThroughCompExpr2L
                 , pullPropRenameThroughIntegerToDouble
                 , pullProjectPayloadThroughSegment
                 , pullProjectPayloadThroughPropRename
                 , pullSelectThroughPairL
                 , mergeDescToRenames
                 , descriptorFromProject
                 , noOpPropRename1
                 ]
                 
redundantRulesBottomUp :: VLRuleSet BottomUpProps
redundantRulesBottomUp = [ pairFromSameSource 
                         , pairedProjections
                         , noOpProject
                         , distDescCardOne
                         , toDescr
                         , noOpPropRename2
                         ]
                         
redundantRulesTopDown :: VLRuleSet TopDownProps
redundantRulesTopDown = [ pruneProjectL
                        , pruneProjectPayload
                        ]
                               
-- Eliminate the pattern that arises from a filter: Combination of CombineVec, RestrictVec and RestrictVec(Not).
  
introduceSelectExpr :: VLRule ()
introduceSelectExpr q =
  $(pattern 'q "R1 ((q1) RestrictVec (CompExpr1L e (q2)))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        
        return $ do
          logRewrite "Redundant.SelectExpr" q
          selectNode <- insert $ UnOp (SelectExpr $(v "e")) $(v "q1")
          void $ relinkToNew q $ UnOp (ProjectAdmin (DescrIdentity, PosNumber)) selectNode |])
  
restrictCombineDBV :: VLRule ()
restrictCombineDBV q =
  $(pattern 'q "R1 (CombineVec (qb1) (ToDescr (R1 ((q1) RestrictVec (qb2)))) (ToDescr (R1 ((q2) RestrictVec (NotVec (qb3))))))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        predicate $ $(v "qb1") == $(v "qb2") && $(v "qb1") == $(v "qb3")
        return $ do
          logRewrite "Redundant.RestrictCombine.DBV" q
          void $ relinkToNew q $ UnOp ToDescr $(v "q1") |])

restrictCombinePropLeft :: VLRule ()
restrictCombinePropLeft q =
  $(pattern 'q "R2 (CombineVec (CompExpr1L e1 (q1)) (ToDescr (ProjectAdmin p1 (qs=SelectExpr e2 (q2)))) (ToDescr (R1 ((q3) RestrictVec (NotVec (CompExpr1L e3 (q4)))))))"
    [| do
        -- all selections and predicates must be performed on the same input
        predicate $ $(v "q1") == $(v "q2") && $(v "q1") == $(v "q3") && $(v "q1") == $(v "q4")
        -- all selection expressions must be the same
        predicate $ $(v "e1") == $(v "e2") && $(v "e1") == $(v "e3")
        
        case $(v "p1") of
          (DescrIdentity, PosNumber) -> return ()
          _                          -> fail "no match"
        
        return $ do
          logRewrite "Redundant.RestrictCombine.PropLeft/2" q
          void $ relinkToNew q $ UnOp (ProjectRename (STPosCol, STNumber)) $(v "qs") |])
  
-- Clean up the remains of a selection pattern after the CombineVec
-- part has been removed by rule Redundant.RestrictCombine.PropLeft
cleanupSelect :: VLRule ()
cleanupSelect q =
  $(pattern 'q "(ProjectRename p1 (qs=SelectExpr e1 (q1))) PropRename (Segment (ProjectAdmin p2 (SelectExpr e2 (q2))))"
    [| do
        predicate $ $(v "e1") == $(v "e2")
        predicate $ $(v "q1") == $(v "q2")
        
        case $(v "p1") of
          (STPosCol, STNumber) -> return ()
          _                    -> fail "no match"
          
        case $(v "p2") of
          (DescrIdentity, PosNumber) -> return ()
          _                          -> fail "no match"
        
        return $ do
          logRewrite "Redundant.CleanupSelect" q
          void $ relinkToNew q $ UnOp (ProjectAdmin (DescrPosCol, PosNumber)) $(v "qs") |])
  
{- 
ifToSelect :: VLRule ()
ifToSelect q =
  $(pattern 'q "(R2 (CombineVec (CompExpr1 e1) (SelectExpr e2 (_)) ())) PropRename (Segment (ProjectAdmin p (SelectExpr e (qv2))))"
  
-}

{-
foo :: VLRule ()
foo q =
  $(pattern 'q "(R2 (CombineVec (_) (qs1=SelectExpr e (q1)) (_))) PropRename (qs2)"
    [| do
        predicate $ $(v "qs1") == $(v "qs2")
        
        return $ do
          logRewrite "Redundant.foo" q
-}
          
  
pullRestrictThroughPair :: VLRule ()
pullRestrictThroughPair q =
  $(pattern 'q "(R1 ((qp1=ProjectL _ (q1)) RestrictVec (qb1))) PairL (R1 ((qp2=ProjectL _ (q2)) RestrictVec (qb2)))"
    [| do
        predicate $ $(v "qb1") == $(v "qb2")
        predicate $ $(v "q1") == $(v "q2")
        
        return $ do
          logRewrite "Redundant.PullRestrictThroughPair" q
          pairNode <- insert $ BinOp PairL $(v "qp1") $(v "qp2")
          restrictNode <- insert $ BinOp RestrictVec pairNode $(v "qb1")
          r1Node <- insert $ UnOp R1 restrictNode
          relinkParents q r1Node |])
          
-- FIXME this rewrite is way too specific.
pullSelectThroughPairL :: VLRule ()
pullSelectThroughPairL q =
  $(pattern 'q "(qp=ProjectAdmin p1 (SelectExpr e1 (q1))) PairL (ProjectAdmin p2 (SelectExpr e2 (q2)))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        predicate $ $(v "p1") == $(v "p2")
        predicate $ $(v "e1") == $(v "e2")
        
        return $ do
          logRewrite "Redundant.PullSelectThroughPairL" q
          relinkParents q $(v "qp") |])

-- Push a RestrictVec through its left input, if this input is a
-- projection operator (ProjectL).
pushRestrictVecThroughProjectL :: VLRule ()
pushRestrictVecThroughProjectL q =
  $(pattern 'q "R1 ((ProjectL p (q1)) RestrictVec (qb))"
    [| do

        return $ do
          logRewrite "Redundant.PushRestrictVecThroughProjectL" q
          restrictNode <- insert $ BinOp RestrictVec $(v "q1") $(v "qb")
          r1Node <- insert $ UnOp R1 restrictNode
          projectNode <- insert $ UnOp (ProjectL $(v "p")) r1Node
          relinkParents q projectNode |])

-- Push a RestrictVec through its left input, if this input is a
-- projection operator (ProjectPayload).
pushRestrictVecThroughProjectPayload :: VLRule ()
pushRestrictVecThroughProjectPayload q =
  $(pattern 'q "R1 ((ProjectPayload p (q1)) RestrictVec (qb))"
    [| do
        return $ do
          logRewrite "Redundant.PushRestrictVecThroughProjectValue" q
          restrictNode <- insert $ BinOp RestrictVec $(v "q1") $(v "qb")
          r1Node <- insert $ UnOp R1 restrictNode
          projectNode <- insert $ UnOp (ProjectPayload $(v "p")) r1Node
          relinkParents q projectNode |])
        
-- Eliminate a projection if the vector is turned into a descriptor vector anyway.
-- FIXME: this could be done in a more general way using property ToDescr.
descriptorFromProject :: VLRule ()
descriptorFromProject q =
  $(pattern 'q "ToDescr (ProjectL _ (q1))"
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
  $(pattern 'q "((qr1) PropRename (q1)) CompExpr2L e ((qr2) PropRename (q2))"
    [| do
       predicate  $ $(v "qr1") == $(v "qr2")
       
       return $ do
         logRewrite "Redundant.PullPropRenameThroughCompExpr2L" q
         compNode <- insert $ BinOp (CompExpr2L $(v "e")) $(v "q1") $(v "q2")
         replace q $ BinOp PropRename $(v "qr1") compNode |])
  
-- Pull PropRename operators through a IntegerToDoubleL operator.
pullPropRenameThroughIntegerToDouble :: VLRule ()
pullPropRenameThroughIntegerToDouble q =
  $(pattern 'q "IntegerToDoubleL ((qr) PropRename (qv))"
    [| do
        return $ do
          logRewrite "Redundant.PullPropRenameThroughIntegerToDouble" q
          castNode <- insert $ UnOp IntegerToDoubleL $(v "qv")
          replace q $ BinOp PropRename $(v "qr") castNode |])
  
-- Try to merge multiple DescToRename operators which reference the same
-- descriptor vector
mergeDescToRenames :: VLRule ()
mergeDescToRenames q =
  $(pattern 'q "DescToRename (d)"
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
  $(pattern 'q "(q1) PairL (q2)"
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
  $(pattern 'q "[ProjectL | ProjectA] ps (q1)"
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
  $(pattern 'q "ToDescr (q1)"
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
  $(pattern 'q "(ProjectL ps1 (q1)) PairL (ProjectL ps2 (q2))"
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
  $(pattern 'q "R1 ((qc) DistDesc (ToDescr (qv)))"
    [| do
        qvProps <- properties $(v "qc")
        predicate $ case card1Prop qvProps of
                      VProp c -> c
                      _       -> error "distDescCardOne: no single property"
       
        let constVal (ConstPL val) = return $ PLConst val
            constVal _             = fail "no match"
       
        
        constProjs <- case constProp qvProps of
          VProp (DBVConst _ cols) -> mapM constVal cols
          _                       -> fail "no match"
          
        return $ do
          logRewrite "Redundant.DistDescCardOne" q
          projNode <- insert $ UnOp (ProjectPayload constProjs) $(v "qv")
          replace q $ UnOp Segment projNode |])
  
pruneProjectL :: VLRule TopDownProps
pruneProjectL q =
  $(pattern 'q "ProjectL _ (q1)"
    [| do
        reqCols <- reqColumnsProp <$> properties q
        case reqCols of
          VProp (Just []) -> return ()
          VProp Nothing   -> return ()
          _               -> fail "no match"

        return $ do
          logRewrite "Redundant.PruneProjectL" q
          relinkParents q $(v "q1") |])

pruneProjectPayload :: VLRule TopDownProps
pruneProjectPayload q =
  $(pattern 'q "ProjectPayload _ (q1)"
    [| do
        reqCols <- reqColumnsProp <$> properties q
        case reqCols of
          VProp (Just []) -> return ()
          VProp Nothing   -> return ()
          _               -> fail "no match"
        return $ do
          logRewrite "Redundant.PruneProjectPayload" q
          relinkParents q $(v "q1") |])
  
pullProjectPayloadThroughSegment :: VLRule ()
pullProjectPayloadThroughSegment q = 
  $(pattern 'q "Segment (ProjectPayload p (q1))"
    [| do
        return $ do
          logRewrite "Redundant.PullProjectPayload.Segment" q
          segmentNode <- insert $ UnOp Segment $(v "q1")
          void $ relinkToNew q $ UnOp (ProjectPayload $(v "p")) segmentNode |])
  
pullProjectPayloadThroughPropRename :: VLRule ()
pullProjectPayloadThroughPropRename q =
  $(pattern 'q "(qr) PropRename (ProjectPayload p (qv))"
    [| do
        return $ do
          logRewrite "Redundant.PullProjectPayload.PropRename" q
          renameNode <- insert $ BinOp PropRename $(v "qr") $(v "qv")
          newNode    <- relinkToNew q $ UnOp (ProjectPayload $(v "p")) renameNode 
          replaceRootWithShape q newNode |])
                                        
-- Elimiante PropRename operators which map from one index space to the same
-- index space. Since PropRename maps from the positions of the left side, both
-- index spaces must be STPosCol. This pattern originates from the pruning of empty
-- Append inputs in VL.Rewrite.PruneEmpty.
-- FIXME rewrite needs a better name.
noOpPropRename1 :: VLRule ()
noOpPropRename1 q =
  $(pattern 'q "(ProjectRename proj (_)) PropRename (q1)"
    [| do
        let s = fst $(v "proj")
            t = snd $(v "proj")

        predicate $ (s == STPosCol) && (s == t)

        return $ do
          logRewrite "Redundant.NoOpPropRename1" q
          relinkParents q $(v "q1") |])
  
unpackProp :: VectorProp a -> a
unpackProp (VProp p) = p
unpackProp _         = error "unpackProp"
  
-- FIXME clean up and document the rewrite, especially the property extraction
noOpPropRename2 :: VLRule BottomUpProps
noOpPropRename2 q =
  $(pattern 'q "(qi1={ } qs1=SelectExpr _ (_)) PropRename (qi2={ } qs2=SelectExpr _ (_))"
    [| do
        -- left and right inputs must originate from the same source.
        predicate $ $(v "qs1") == $(v "qs2")

        propsLeft <- trace ("pattern matched " ++ (show q)) $ properties $(v "qi1")
        propsRight <- properties $(v "qi2")
        propsSource <- properties $(v "qs1")
  
        -- the right input must not have changed its vertical shape
        case verticallyIntactProp propsRight of
          VProp nodes -> predicate $ $(v "qs1") `elem` nodes
          _           -> error "Redundant.NoOpPropRename2: no single vector input"
        
        -- extract the vector type of the right input
        let vt = case vectorTypeProp propsRight of
                   VProp t -> t
                   p       -> error ("foo " ++ (show p))
          
        
        -- if the right input is a value vector, it must be untainted
        case vt of
          ValueVector _ -> 
            case untaintedProp propsRight of
              VProp (Just nodes) -> predicate $ $(v "qs1") `elem` nodes
              VProp Nothing      -> fail "no match"
              _                  -> error "Redundant.NoOpPropRename2: foo"
                                   
          DescrVector     -> return ()
          _               -> error "Redundant.NoOpPropRename2: non-Value/non-Descr vector as input of PropRename"
          
        -- TODO check alignment for PropRename?
  
            -- extract the index space that the PropRename maps to.
        let descrTargetSpace = case unpackProp $ indexSpaceProp propsLeft of
              RenameVectorTransform _ (T tis) -> tis
              _                               -> error "Redundant.NoOpPropRename2: non-Rename index spaces"
              
            -- extract the position space of the result (equals the pos space of the right input,
            -- because it's not changed by PropRename.
            resultPosSpace = case unpackProp $ indexSpaceProp propsRight of
              DBVSpace _ (P pis)         -> pis
              DescrVectorSpace _ (P pis) -> pis
              _                          -> error "Redundant.NoOpPropRename2: non VV/DV index spaces"
            
            -- extract the descr and pos index spaces of the input (SelectExpr).
            (sourceDescrSpace, sourcePosSpace) = case unpackProp $ indexSpaceProp propsSource of
              DBVSpace (D dis) (P pis) -> (dis, pis)
              _                        -> error "Redundant.NoOpPropRename2: non-DBV index spaces"
            
        descrProj <- case descrTargetSpace of
            s | s == sourceDescrSpace -> return DescrIdentity  
            s | s == sourcePosSpace   -> return DescrPosCol
            _ | otherwise             -> fail "no match"
            
        posProj <- case resultPosSpace of
            s | s == sourcePosSpace             -> return PosNumber
            s | s `numberedFrom` sourcePosSpace -> return PosNumber
            _ | otherwise                       -> fail "no match"
  
        return $ do
          logRewrite "Redundant.NoOpPropRename2" q
          let projOp = UnOp (ProjectAdmin (descrProj, posProj)) $(v "qs1")
          case vt of
            -- if the right PropRename input is a ValueVector, we just modify positions and descriptors
            ValueVector _ -> void $ relinkToNew q projOp
            -- for a DescrVector, we insert an additional ToDescr cast on top
            DescrVector   -> do
              projNode <- insert projOp
              void $ relinkToNew q $ UnOp ToDescr projNode
            _ -> error "impossible" |])
        
          
