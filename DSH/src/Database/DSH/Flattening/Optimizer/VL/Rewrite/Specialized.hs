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
  
introduceSpecializedOperators :: DagRewrite VL Bool
introduceSpecializedOperators = preOrder inferBottomUp specializedRules
                                
specializedRules :: RuleSet VL BottomUpProps
specializedRules = [ cartProd 
                   , equiJoin ]
                   
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
cartProd :: Rule VL BottomUpProps
cartProd q =
  $(pattern [| q |] "R1 ((distInput) DistLift (ToDescr (right=R1 ((leftInput) DistDesc (ToDescr (rightInput))))))"
    [| do
        predicate $ $(v "distInput") == $(v "rightInput")

        s1 <- liftM vectorSchemaProp $ properties $(v "leftInput")
        s2 <- liftM vectorSchemaProp $ properties $(v "rightInput")
        
        let (w1, w2) = (schemaWidth s1, schemaWidth s2)

        return $ do
          logRewriteM "Specialized.CartProd" q
          let prodOp = BinOp CartProductFlat $(v "leftInput") $(v "rightInput")
          prodNode <- insertM prodOp
          let projLeft = UnOp (ProjectL [1 .. w1]) prodNode
              projRight = UnOp (ProjectL [(w1 + 1) .. (w1 + w2)]) prodNode
          projLeftNode <- insertM projLeft
          projRightNode <- insertM projRight
          relinkParentsM q projRightNode
          relinkParentsM $(v "right") projLeftNode |])
  
mapColumnToSide :: Int -> Int -> Int -> Int
mapColumnToSide leftWidth rightWidth i =
  if i < leftWidth 
  then i
  else i - (leftWidth + 1)
  
equiJoin :: Rule VL BottomUpProps
equiJoin q = 
  $(pattern [| q |] "R1 ((q1=(qi1) CartProductFlat (qi2)) RestrictVec (VecBinOpSingle p (q2=(_) CartProductFlat (_))))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        s1 <- liftM vectorSchemaProp $ properties $(v "q1")
        s2 <- liftM vectorSchemaProp $ properties $(v "q2")

        let (vecOp, leftArgCol, rightArgCol) = $(v "p")
        predicate $ vecOp == Eq

        let (w1, w2) = (schemaWidth s1, schemaWidth s2)
              
        return $ do
          logRewriteM "Specialized.EquiJoin" q
          let mc = mapColumnToSide w1 w2
              joinOp = BinOp (ThetaJoinFlat (Eq, mc leftArgCol, mc rightArgCol)) $(v "qi1") $(v "qi2")
          joinNode <- insertM joinOp
          relinkParentsM q joinNode |])
                              
          
       
       