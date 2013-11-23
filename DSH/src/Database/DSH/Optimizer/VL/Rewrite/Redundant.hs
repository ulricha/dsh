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
import Database.DSH.Optimizer.VL.Rewrite.MergeProjections

removeRedundancy :: VLRewrite Bool
removeRedundancy = iteratively $ sequenceRewrites [ cleanup
                                                  , applyToAll noProps redundantRules
                                                  , applyToAll inferBottomUp redundantRulesBottomUp
                                                  -- , applyToAll inferTopDown redundantRulesTopDown
                                                  ]

cleanup :: VLRewrite Bool
cleanup = iteratively $ sequenceRewrites [ mergeProjections
                                         , optExpressions
                                         ]

redundantRules :: VLRuleSet ()
redundantRules = [ introduceSelectExpr ]

redundantRulesBottomUp :: VLRuleSet BottomUpProps
redundantRulesBottomUp = [ pairFromSameSource
                         -- , pairedProjections
                         -- , noOpProject
                         , distDescCardOne
                         ]

redundantRulesTopDown :: VLRuleSet TopDownProps
redundantRulesTopDown = []

introduceSelectExpr :: VLRule ()
introduceSelectExpr q =
  $(pattern 'q "R1 ((q1) RestrictVec (CompExpr1L e (q2)))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.SelectExpr" q
          void $ replaceWithNew q $ UnOp (SelectExpr $(v "e")) $(v "q1") |])

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
          _                                                                      -> fail "no match"
        return $ do
          logRewrite "Redundant.PairFromSame" q
          replace q $(v "q1") |])

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

{-

FIXME ProjectL -> VLProject

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
              replace q $(v "q1")
            else do
              logRewrite "Redundant.PairedProjections.Reorder" q
              let op = UnOp (VLProject $ map Column1 $ $(v "ps1") ++ $(v "ps2")) $(v "q1")
              projectNode <- insert op
              replace q projectNode |])
-}              

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

