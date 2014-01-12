{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Rewrite.Redundant (removeRedundancy) where

import Control.Monad
import Control.Applicative

import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data

import Database.DSH.Optimizer.Common.Rewrite
import Database.DSH.Optimizer.VL.Properties.Types
import Database.DSH.Optimizer.VL.Properties.VectorType
import Database.DSH.Optimizer.VL.Rewrite.Common
import Database.DSH.Optimizer.VL.Rewrite.Expressions

removeRedundancy :: VLRewrite Bool
removeRedundancy = 
    iteratively $ sequenceRewrites [ cleanup
                                   , applyToAll noProps redundantRules
                                   , applyToAll inferBottomUp redundantRulesBottomUp
                                   , applyToAll inferTopDown redundantRulesTopDown
                                   ]

cleanup :: VLRewrite Bool
cleanup = iteratively $ sequenceRewrites [ optExpressions ]

redundantRules :: VLRuleSet ()
redundantRules = [ introduceSelect, simpleSort ]

redundantRulesBottomUp :: VLRuleSet BottomUpProps
redundantRulesBottomUp = [ distPrimConstant
                         , distDescConstant
                         , pushZipThroughProjectLeft
                         , pushZipThroughProjectRight
                         , sameInputZip
                         ]

redundantRulesTopDown :: VLRuleSet TopDownProps
redundantRulesTopDown = [ unreferencedDistSeg ]

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

-- | Replace a DistPrim operator with a projection if its value input
-- is constant.
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

-- | Replace a DistDesc operator with a projection if its value input
-- is constant and consists of only one tuple.
distDescConstant :: VLRule BottomUpProps
distDescConstant q =
  $(pattern 'q "R1 ((qv) DistDesc (qd))"
    [| do
        pv <- properties $(v "qv")
        VProp True <- return $ card1Prop pv

        let constVal (ConstPL val) = return $ Constant1 val
            constVal _             = fail "no match"

        VProp (DBVConst _ cols) <- return $ constProp pv
        constProjs              <- mapM constVal cols

        return $ do
          logRewrite "Redundant.DistDesc.Constant" q
          void $ replaceWithNew q $ UnOp (Project constProjs) $(v "qd") |])

-- | If a vector is distributed over an inner vector in a segmented
-- way, check if the vector's columns are actually referenced/required
-- downstream. If not, we can remove the DistSeg altogether, as the
-- shape of the inner vector is not changed by DistSeg.
unreferencedDistSeg :: VLRule TopDownProps
unreferencedDistSeg q =
  $(pattern 'q  "R1 ((_) DistSeg (qd))"
    [| do
        VProp (Just reqCols) <- reqColumnsProp <$> properties q
        predicate $ null reqCols

        return $ do
          logRewrite "Redundant.UnreferencedDistSeg" q
          void $ replace q $(v "qd") |])
        
          
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
          void $ replaceWithNew q $ UnOp (Project (ps ++ ps)) $(v "q1") |])


-- | Employ a specialized operator if the sorting criteria are simply
-- a selection of columns from the input vector.
simpleSort :: VLRule ()
simpleSort q =
  $(pattern 'q "R1 (qs=(Project ps (q1)) Sort (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
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
