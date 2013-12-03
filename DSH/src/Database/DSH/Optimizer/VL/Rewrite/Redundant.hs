{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Rewrite.Redundant (removeRedundancy) where
       
import Debug.Trace
import Text.Printf

import Control.Monad

import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data

import Database.DSH.Optimizer.Common.Rewrite
import Database.DSH.Optimizer.VL.Properties.Types
import Database.DSH.Optimizer.VL.Properties.VectorType
import Database.DSH.Optimizer.VL.Rewrite.Common
import Database.DSH.Optimizer.VL.Rewrite.Expressions

removeRedundancy :: VLRewrite Bool
removeRedundancy = iteratively $ sequenceRewrites [ cleanup
                                                  , applyToAll noProps redundantRules
                                                  , applyToAll inferBottomUp redundantRulesBottomUp
                                                  -- , applyToAll inferTopDown redundantRulesTopDown
                                                  ]

cleanup :: VLRewrite Bool
cleanup = iteratively $ sequenceRewrites [ optExpressions ]

redundantRules :: VLRuleSet ()
redundantRules = [ introduceSelectExpr ]

redundantRulesBottomUp :: VLRuleSet BottomUpProps
redundantRulesBottomUp = [ distPrimConstant
                         , pushPairLThroughProjectLeft
                         , pushPairLThroughProjectRight
                         , sameInputPairL
                         ]

redundantRulesTopDown :: VLRuleSet TopDownProps
redundantRulesTopDown = []

introduceSelectExpr :: VLRule ()
introduceSelectExpr q =
  $(pattern 'q "R1 ((q1) RestrictVec (VLProject es (q2)))"
    [| do
        [e] <- return $(v "es")
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.SelectExpr" q
          void $ replaceWithNew q $ UnOp (SelectExpr $(v "e")) $(v "q1") |])

{-

FIXME really necessary?

-- Remove a ProjectL or ProjectA operator that does not change the column layout
noOpProject :: VLRule BottomUpProps
noOpProject q =
  $(pattern 'q "[ProjectL | ProjectA] ps (q1)"
    [| do
        vt <- liftM vectorTypeProp $ properties $(v "q1")
        predicate $ vectorWidth vt == length $(v "ps")
        predicate $ all (uncurry (==)) $ zip ([1..] :: [DBCol]) $(v "ps")

        return $ do
          logRewrite "Redundant.NoOpProject" q
          replace q $(v "q1") |])
-}          

distPrimConstant :: VLRule BottomUpProps
distPrimConstant q =
  $(pattern 'q "R1 ((qp) DistPrim (qv))"
    [| do
        qvProps <- properties $(v "qp")
        let constVal (ConstPL val) = return $ Constant1 val
            constVal _             = fail "no match"


        constProjs <- case constProp qvProps of
          VProp (DBVConst _ cols) -> mapM constVal cols
          _                       -> fail "no match"
          
        return $ do
          logRewrite "Redundant.DistPrim.Constant" q
          void $ replaceWithNew q $ UnOp (VLProject constProjs) $(v "qv") |])
          
        

-- If we encounter a DistDesc which distributes a vector of size one
-- over a descriptor (that is, the cardinality of the descriptor
-- vector does not change), replace the DistDesc by a projection which
-- just adds the (constant) values from the value vector
distDescCardOne :: VLRule BottomUpProps
distDescCardOne q =
  $(pattern 'q "R1 ((qc) DistDesc (qv))"
    [| do
        qvProps <- properties $(v "qc")
        predicate $ case card1Prop qvProps of
                      VProp c -> c
                      _       -> error "distDescCardOne: no single property"

        let constVal (ConstPL val) = return $ Constant1 val
            constVal _             = fail "no match"


        constProjs <- case constProp qvProps of
          VProp (DBVConst _ cols) -> mapM constVal cols
          _                       -> fail "no match"

        return $ do
          logRewrite "Redundant.DistDescCardOne" q
          projNode <- insert $ UnOp (VLProject constProjs) $(v "qv")
          void $ replaceWithNew q $ UnOp Segment projNode |])
          
shiftCols :: Int -> Expr1 -> Expr1
shiftCols offset expr =
    case expr of
        BinApp1 o e1 e2 -> BinApp1 o (shiftCols offset e1) (shiftCols offset e2)
        UnApp1 o e1     -> UnApp1 o (shiftCols offset e1)
        Column1 i       -> Column1 (offset + i)
        Constant1 c     -> Constant1 c

-- | Push a PairL operator through a projection in the left input
pushPairLThroughProjectLeft :: VLRule BottomUpProps
pushPairLThroughProjectLeft q =
  $(pattern 'q "(VLProject es (q1)) PairL (q2)"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q2")

        return $ do
          let es' = $(v "es") ++ [ Column1 $ w1 + i | i <- [1 .. w2] ]
          qp <- insert $ BinOp PairL $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (VLProject es') qp |])

-- | Push a PairL operator through a projection in the right input
pushPairLThroughProjectRight :: VLRule BottomUpProps
pushPairLThroughProjectRight q =
  $(pattern 'q "(q1) PairL (VLProject es (q2))"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
               
          let es' = [ Column1 i | i <- [1 .. w1] ] ++ [ shiftCols w1 e | e <- $(v "es") ]

          qp <- insert $ BinOp PairL $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (VLProject es') qp |])
          
-- | Replace a PairL operaor with a projection if both inputs are the same.
sameInputPairL :: VLRule BottomUpProps
sameInputPairL q =
  $(pattern 'q "(q1) PairL (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        
        return $ do
          let ps = map Column1 [1 .. w]
          void $ replaceWithNew q $ UnOp (VLProject (ps ++ ps)) $(v "q1") |])
