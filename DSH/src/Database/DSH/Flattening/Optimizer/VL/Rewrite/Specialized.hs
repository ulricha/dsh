{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.Specialized where

import Debug.Trace

import Control.Monad
import Control.Applicative

-- FIXME hiding is not acceptable, fix names
import Database.Algebra.Rewrite hiding (D)
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data
import Database.Algebra.X100.Properties.AbstractDomains

import Optimizer.Common.Match
import Optimizer.Common.Traversal
  
import Optimizer.VL.Properties.Types
import Optimizer.VL.Properties.VectorType
import Optimizer.VL.Rewrite.Common
import Optimizer.VL.Rewrite.Redundant
  
introduceSpecializedOperators :: VLRewrite Bool
introduceSpecializedOperators = iteratively $ sequenceRewrites [ normalize
                                                               , preOrder inferBottomUp specializedRules ]

normalize :: VLRewrite Bool
normalize = sequenceRewrites [ preOrder noProps normalizeRules
                             , preOrder inferBottomUp normalizePropRules ]
            
normalizeRules :: VLRuleSet ()
normalizeRules = [ descriptorFromProject
                 , mergeStackedDistDesc
                 , pullProjectLThroughDistLift ]
                 
normalizePropRules :: VLRuleSet BottomUpProps
normalizePropRules = [ redundantDistLift
                     , pruneFilteringDistLift ]
                                
specializedRules :: VLRuleSet BottomUpProps
specializedRules = [ cartProd 
                   , thetaJoin ]
                   
{- Normalize the cartesian product pattern by pulling horizontal
modifications (projections, general expressions) as high as possible
-}
                   
-- If a DistLift lifts the output of a projection, apply the projection after
-- the DistLift. This is necessary to keep all payload data as long as necessary
-- and thereby normalize cartesian product patterns.
pullProjectLThroughDistLift :: VLRule ()
pullProjectLThroughDistLift q =
  $(pattern [| q |] "R1 ((ProjectL p (qv)) DistLift (qd))"
    [| do
        return $ do
          logRewrite "Specialized.PullProjectLThroughDistLift" q
          liftNode <- insert $ BinOp DistLift $(v "qv") $(v "qd")
          r1Node   <- insert $ UnOp R1 liftNode
          void $ relinkToNew q $ UnOp (ProjectL $(v "p")) r1Node |])
  
-- Eliminate a common pattern where the output of a cartesian product is turned into a
-- descriptor vector and used to lift one of the product inputs. This is redundant because
-- the CartProduct operator already provides the data originating from the lift.

-- FIXME this is propably just a special case of rule pruneFilteringDistLift
redundantDistLift:: VLRule BottomUpProps
redundantDistLift q =
  $(pattern [| q |] "R1 ((qv) DistLift (ToDescr (qp=(qv1) CartProductFlat (qv2))))"
    [| do
        predicate $ $(v "qv") == $(v "qv1") || $(v "qv") == $(v "qv2")

        vt1 <- vectorTypeProp <$> properties $(v "qv1")
        let w1 = case vt1 of
                   VProp (ValueVector w) -> w
                   _                     -> error "redundantDistLift: no ValueVector on the left side"

        vt2 <- vectorTypeProp <$> properties $(v "qv2")
        let w2 = case vt2 of
                   VProp (ValueVector w) -> w
                   _                     -> error "redundantDistLift: no ValueVector on the right side"
                
        return $ do
          let (p, msg) = if $(v "qv") == $(v "qv1")
                         then ([1 .. w1], "Specialized.RedundantDistLift.Left")
                         else ([(w1 + 1) .. w2], "Specialized.RedundantDistLift.Right")
          logRewrite msg q
          void $ relinkToNew q $ UnOp (ProjectL p) $(v "qp") |])
  
-- FIXME This matches only a special case: If DistLift is to be
-- replaced by the right input, the original descriptor before it is
-- overwritten with the positions to align with the left side must be
-- kept/restored.
pruneFilteringDistLift :: VLRule BottomUpProps
pruneFilteringDistLift q =
  $(pattern [| q |] "R1 ((q1) DistLift (ToDescr (qp=ProjectAdmin _ (q2))))"
    [| do
        props1 <- trace "match pattern" $ properties $(v "q1")
        propsp <- properties $(v "qp")
        
        {- The following properties need to hold:
           1. q2.descr must be a subdomain of the domain of q1.pos
           2. q2 payload must be untainted with respect to the node 
              from where the q1.pos domain originates
        -}
       
        let q1Pos = case indexSpaceProp props1 of
              VProp (DBVSpace _ (P pis)) -> pis
              _                          -> error "foo"
              
            qpDescr = case indexSpaceProp propsp of
              VProp (DBVSpace (D dis) _) -> dis
              _                          -> error "foo"
              
            untaintedNodes = case untaintedProp propsp of
              VProp (Just nodes) -> nodes
              _                  -> []
        
        let q1OriginNode = case domainNode q1Pos of
              Just n  -> n
              Nothing -> error "foo"
              
        predicate $ subDomain qpDescr q1Pos
        
        predicate $ q1OriginNode `elem` untaintedNodes
        
        return $ do
          logRewrite "Specialized.PruneFilteringDistLift" q
          relinkParents q $(v "q2") |])
                   
{-

Introduce a specialized CartProd operator:

Rewrite the following pattern into a CartProd operator:

        R1
        |
        DistLift
       /|
      / ToDescr
     /  |
    q2  R1
        |
        DistDesc
       /\
      /  \
     q1   \
           \
           ToDescr
            |
            q2

This pattern first distributes q1 over q2, producing a vector with the payload data of q1
and cardinality q1 x q2. Next, q2 is distributed (with lifted semantics) over the resulting
descriptor, producing a vector with the payload data of q2 and the same cardinality.

This pattern can be rewritten into a specialized CartProd operator which keeps the data of
inputs.

     ProjectL    ProjectL
          \        /
           \      /
            \    /
           CartProd
             /\
            /  \
           q1   q2
              
-}
cartProd :: VLRule BottomUpProps
cartProd q =
  $(pattern [| q |] "R1 ((distInput) DistLift (d=ToDescr (right=R1 ((leftInput) DistDesc (ToDescr (rightInput))))))"
    [| do
        predicate $ $(v "distInput") == $(v "rightInput")

        s1 <- vectorTypeProp <$> properties $(v "leftInput")
        s2 <- vectorTypeProp <$> properties $(v "rightInput")
        
        let (w1, w2) = (vectorWidth s1, vectorWidth s2)

        return $ do
          logRewrite "Specialized.CartProd" q
          let prodOp = BinOp CartProductFlat $(v "leftInput") $(v "rightInput")
          prodNode <- insert prodOp
          let projLeft = UnOp (ProjectL [1 .. w1]) prodNode
              projRight = UnOp (ProjectL [(w1 + 1) .. (w1 + w2)]) prodNode
          projLeftNode <- insert projLeft
          projRightNode <- insert projRight
          relinkParents q projRightNode
          relinkParents $(v "right") projLeftNode |])

{- 

Introduce a specialized join operator to replace a cartesian product
with a selection (RestrictVec) on top.

                    RestrictVec
                      |     \
                      |      \
                      |   CompExpr1(pred)
                      |       /
                      |      /
                      |     /
                  CartProductFlat
                        /\
                       /  \
                      /    \
                     q1     q2 

is rewritten into

                 ThetaJoinFlat(pred)
                        /\
                       /  \
                      /    \
                     q1     q2 
-}

thetaJoin :: VLRule BottomUpProps
thetaJoin q = 
  $(pattern [| q |] "R1 ((q1=(qi1) CartProductFlat (qi2)) RestrictVec (CompExpr1L expr (q2=(_) CartProductFlat (_))))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Specialized.EquiJoin" q
          let joinOp = BinOp (ThetaJoinFlat $(v "expr")) $(v "qi1") $(v "qi2")
          joinNode <- insert joinOp
          relinkParents q joinNode |])
