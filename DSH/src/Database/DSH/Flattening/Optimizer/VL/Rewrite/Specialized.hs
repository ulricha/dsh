{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.Specialized where

import Debug.Trace

import Control.Monad

import Database.Algebra.Rewrite
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data
  
import Optimizer.VL.Properties.Types
import Optimizer.VL.Properties.VectorSchema
import Optimizer.VL.Rewrite.Common
  
introduceSpecializedOperators :: VLRewrite Bool
introduceSpecializedOperators = preOrder inferBottomUp specializedRules
                                
specializedRules :: VLRuleSet BottomUpProps
specializedRules = [ cartProd 
                   , thetaJoin ]
                   
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

        s1 <- liftM vectorSchemaProp $ properties $(v "leftInput")
        s2 <- liftM vectorSchemaProp $ properties $(v "rightInput")
        
        let (w1, w2) = (schemaWidth s1, schemaWidth s2)

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
  $(pattern [| q |] "R1 ((q1=(qi1) CartProductFlat (qi2)) RestrictVec (CompExpr1 expr (q2=(_) CartProductFlat (_))))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Specialized.EquiJoin" q
          let joinOp = BinOp (ThetaJoinFlat $(v "expr")) $(v "qi1") $(v "qi2")
          joinNode <- insert joinOp
          relinkParents q joinNode |])
