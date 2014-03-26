{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Rewrite.Redundant (removeRedundancy) where

import Control.Monad
import Control.Applicative

import Database.Algebra.Dag.Common

import Database.DSH.VL.Lang
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
                                   , applyToAll inferProperties redundantRulesAllProps
                                   ]

cleanup :: VLRewrite Bool
cleanup = iteratively $ sequenceRewrites [ optExpressions ]

redundantRules :: VLRuleSet ()
redundantRules = [ introduceSelect
                 , simpleSort 
                 , pullProjectPropRename
                 , pullProjectPropReorder
                 ]

redundantRulesBottomUp :: VLRuleSet BottomUpProps
redundantRulesBottomUp = [ distPrimConstant
                         , distDescConstant
                         , sameInputZip
                         , sameInputZipProject
                         , sameInputZipProjectLeft
                         , sameInputZipProjectRight
                         ]

redundantRulesAllProps :: VLRuleSet Properties
redundantRulesAllProps = [ unreferencedAlign
                         , unreferencedProject
                         -- , alignedOnlyLeft
                         ]

introduceSelect :: VLRule ()
introduceSelect q =
  $(pattern 'q "R1 ((q1) Restrict (Project es (q2)))"
    [| do
        [e] <- return $(v "es")
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.Select" q
          void $ replaceWithNew q $ UnOp (Select $(v "e")) $(v "q1") |])

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
unreferencedAlign :: VLRule Properties
unreferencedAlign q =
  $(pattern 'q  "R1 ((_) Align (qd))"
    [| do
        VProp (Just reqCols) <- reqColumnsProp <$> td <$> properties q
        predicate $ null reqCols

        return $ do
          logRewrite "Redundant.Unreferenced.Align" q
          void $ replace q $(v "qd") |])

unreferencedProject :: VLRule Properties
unreferencedProject q =
  $(pattern 'q "Project _ (q1)"
     [| do
         VProp (Just reqCols) <- reqColumnsProp <$> td <$> properties q
         predicate $ null reqCols
  
         return $ do
           logRewrite "Redundant.Unreferenced.Project" q
           void $ replace q $(v "q1") |])

{-
-- Housekeeping rule: Align takes only
alignedOnlyLeft :: VLRule Properties
alignedOnlyLeft q =
  $(pattern 'q "(q1) Align (Project _ (q2))"
    [| do
        -- check that only columns from the right input (outer vector)
        -- are required
        props                 <- properties q
        VProp (Just reqCols)  <- return $ reqColumnsProp $ td props
        VProp (ValueVector w) <- return $ vectorTypeProp $ bu props
        predicate $ all (<= w) reqCols
  
        return $ do
          logRewrite "Redundant.Align.Project" q
          void $ replaceWithNew q $ BinOp Align $(v "q1") $(v "q2") |])
-}
          
shiftCols :: Int -> Expr1 -> Expr1
shiftCols offset expr =
    case expr of
        BinApp1 o e1 e2 -> BinApp1 o (shiftCols offset e1) (shiftCols offset e2)
        UnApp1 o e1     -> UnApp1 o (shiftCols offset e1)
        Column1 i       -> Column1 (offset + i)
        Constant1 c     -> Constant1 c

-- | Replace a Zip operaor with a projection if both inputs are the same.
sameInputZip :: VLRule BottomUpProps
sameInputZip q =
  $(pattern 'q "(q1) Zip (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        
        return $ do
          logRewrite "Redundant.Zip" q
          let ps = map Column1 [1 .. w]
          void $ replaceWithNew q $ UnOp (Project (ps ++ ps)) $(v "q1") |])

sameInputZipProject :: VLRule BottomUpProps
sameInputZipProject q =
  $(pattern 'q "(Project ps1 (q1)) Zip (Project ps2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.Zip.Project" q
          void $ replaceWithNew q $ UnOp (Project ($(v "ps1") ++ $(v "ps2"))) $(v "q1") |])

sameInputZipProjectLeft :: VLRule BottomUpProps
sameInputZipProjectLeft q =
  $(pattern 'q "(Project ps1 (q1)) Zip (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip.Project.Left" q
          let proj = $(v "ps1") ++ (map Column1 [1 .. w])
          void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

sameInputZipProjectRight :: VLRule BottomUpProps
sameInputZipProjectRight q =
  $(pattern 'q "(q1) Zip (Project ps2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip.Project.Right" q
          let proj = (map Column1 [1 .. w]) ++ $(v "ps2")
          void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])


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

------------------------------------------------------------------------------
-- Projection pullup

-- Motivation: In order to eliminate or pull up sorting operations in
-- VL rewrites or subsequent stages, payload columns which might
-- induce sort order should be available as long as possible. We
-- assume that the cost of having unrequired columns around is
-- negligible (best case: column store).

pullProjectPropRename :: VLRule ()
pullProjectPropRename q =
  $(pattern 'q "(qp) PropRename (Project proj (qv))"
    [| do
         return $ do
           logRewrite "Redundant.Project.PropRename" q
           renameNode <- insert $ BinOp PropRename $(v "qp") $(v "qv")
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) renameNode |])

pullProjectPropReorder :: VLRule ()
pullProjectPropReorder q =
  $(pattern 'q "R1 ((qp) PropReorder (Project proj (qv)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.Reorder" q
           reorderNode <- insert $ BinOp PropReorder $(v "qp") $(v "qv")
           r1Node      <- insert $ UnOp R1 reorderNode
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node |])
