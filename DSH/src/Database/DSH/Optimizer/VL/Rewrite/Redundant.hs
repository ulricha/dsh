{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Rewrite.Redundant (removeRedundancy) where
       
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
redundantRules = [ introduceSelect
                 , simpleSort
                 , zipProject
                 ]

redundantRulesBottomUp :: VLRuleSet BottomUpProps
redundantRulesBottomUp = [ distPrimConstant
                         -- , pushZipThroughProjectLeft
                         -- , pushZipThroughProjectRight
                         , sameInputZip
                         ]

redundantRulesTopDown :: VLRuleSet TopDownProps
redundantRulesTopDown = []

introduceSelect :: VLRule ()
introduceSelect q =
  $(pattern 'q "R1 ((q1) Restrict (Project es (q2)))"
    [| do
        [e] <- return $(v "es")
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.Select" q
          void $ replaceWithNew q $ UnOp (Select $(v "e")) $(v "q1") |])

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
          void $ replaceWithNew q $ UnOp (Project constProjs) $(v "qv") |])
          
        

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
          projNode <- insert $ UnOp (Project constProjs) $(v "qv")
          void $ replaceWithNew q $ UnOp Segment projNode |])
          
shiftCols :: Int -> Expr1 -> Expr1
shiftCols offset expr =
    case expr of
        BinApp1 o e1 e2 -> BinApp1 o (shiftCols offset e1) (shiftCols offset e2)
        UnApp1 o e1     -> UnApp1 o (shiftCols offset e1)
        Column1 i       -> Column1 (offset + i)
        Constant1 c     -> Constant1 c

-- | Push a Zip operator through a projection in the left input
pushZipThroughProjectLeft :: VLRule BottomUpProps
pushZipThroughProjectLeft q =
  $(pattern 'q "(Project es (q1)) Zip (q2)"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q2")

        return $ do
          let es' = $(v "es") ++ [ Column1 $ w1 + i | i <- [1 .. w2] ]
          qp <- insert $ BinOp Zip $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project es') qp |])

-- | Push a Zip operator through a projection in the right input
pushZipThroughProjectRight :: VLRule BottomUpProps
pushZipThroughProjectRight q =
  $(pattern 'q "(q1) Zip (Project es (q2))"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
               
          let es' = [ Column1 i | i <- [1 .. w1] ] ++ [ shiftCols w1 e | e <- $(v "es") ]

          qp <- insert $ BinOp Zip $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project es') qp |])
          
-- | Replace a Zip operaor with a projection if both inputs are the same.
sameInputZip :: VLRule BottomUpProps
sameInputZip q =
  $(pattern 'q "(q1) Zip (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        
        return $ do
          let ps = map Column1 [1 .. w]
          logRewrite "Redundant.Zip.SameInput" q
          void $ replaceWithNew q $ UnOp (Project (ps ++ ps)) $(v "q1") |])

zipProject :: VLRule ()
zipProject q =
  $(pattern 'q "(Project es1 (q1)) Zip (Project es2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.Zip.Project" q
          void $ replaceWithNew q $ UnOp (Project ($(v "es1") ++ $(v "es2"))) $(v "q1") |])

-- | Employ a specialized operator if the sorting criteria are simply
-- a selection of columns from the input vector.
simpleSort :: VLRule ()
simpleSort q =
  $(pattern 'q "R1 (qs=(Project ps (q1)) Sort (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.Sort.Simple" q
          qs <- insert $ UnOp (SortSimple $(v "ps")) $(v "q1")
          void $ replaceWithNew q $ UnOp R1 qs 
          r2Parents <- lookupR2Parents $(v "qs")

          -- If there are any R2 nodes linking to the original sort operators
          -- (i.e. there are inner vectors to which changes must be propagated),
          -- they have to be rewired to the new SortSimple operator.
          if not $ null r2Parents
            then do
              qr2' <- insert $ UnOp R2 qs
              mapM_ (\qr2 -> replace qr2 qr2') r2Parents
            else return () |])
