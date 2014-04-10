{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Rewrite.Redundant (removeRedundancy) where

import Control.Monad
import Control.Applicative

import Database.Algebra.Dag.Common

import Database.DSH.VL.Lang
import Database.DSH.Common.Lang
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
                 , sortProject
                 , pullProjectPropRename
                 , pullProjectPropReorder
                 , pullProjectRestrict
                 , scalarConditional
                 ]

redundantRulesBottomUp :: VLRuleSet BottomUpProps
redundantRulesBottomUp = [ distPrimConstant
                         , distDescConstant
                         , sameInputZip
                         , sameInputZipProject
                         , sameInputZipProjectLeft
                         , sameInputZipProjectRight
                         , alignParents
                         -- , stackedAlign
                         ]

redundantRulesAllProps :: VLRuleSet Properties
redundantRulesAllProps = [ unreferencedAlign
                         , alignedOnlyLeft
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
  $(pattern 'q  "R1 ((q1) Align (q2))"
    [| do
        VProp (Just reqCols)   <- reqColumnsProp <$> td <$> properties q
        VProp (ValueVector w1) <- vectorTypeProp <$> bu <$> properties $(v "q1")
        VProp (ValueVector w2) <- vectorTypeProp <$> bu <$> properties $(v "q2")
  
        -- Check that only columns from the right input are required
        predicate $ all (> w1) reqCols

        return $ do
          logRewrite "Redundant.Unreferenced.Align" q

          -- FIXME HACKHACKHACK
          let padProj = [ Constant1 $ VLInt 42 | _ <- [1..w1] ]
                        ++
                        [ Column1 i | i <- [1..w2] ]

          void $ replaceWithNew q $ UnOp (Project padProj) $(v "q2") |])

nonAlignOp :: AlgNode -> VLMatch p Bool
nonAlignOp n = do
    op <- getOperator n
    case op of
        BinOp Align _ _ -> return False
        _               -> return True

-- | The Align operator keeps shape and columns of its right
-- input. When this right input is referenced by other operators than
-- Align, we can move this operators to the Align output.
-- 
-- This is beneficial if a composed expression depends on the Align
-- output (some lifted environment value) as well as the original
-- (inner) vector. In that case, we can rewrite things such that only
-- the Align operator is referenced (not its right input). In
-- consequence, The expression has only one source and can be merged
-- into a projection.
alignParents :: VLRule BottomUpProps
alignParents q =
  $(pattern 'q "R1 ((q1) Align (q2))"
     [| do
         parentNodes     <- getParents $(v "q2")
         nonAlignParents <- filterM nonAlignOp parentNodes
         predicate $ not $ null nonAlignParents

         VProp (ValueVector w1) <- vectorTypeProp <$> properties $(v "q1")
         VProp (ValueVector w2) <- vectorTypeProp <$> properties $(v "q2")

         return $ do
             logRewrite "Redundant.Align.Parents" q

             -- First, insert a projection on top of Align that leaves
             -- only the columns from Align's right input.
             let origColsProj = [ Column1 $ w1 + i | i <- [1 .. w2] ]
             projNode <- insert $ UnOp (Project origColsProj) q
  
             -- Then, re-link all parents of the right Align input to
             -- the projection.
             forM_ nonAlignParents $ \p -> replaceChild p $(v "q2") projNode |])

-- | If an outer vector is aligned multiple times with some inner
-- vector (i.e. stacked Align operators with the same left input), one
-- Align is sufficient.
stackedAlign :: VLRule BottomUpProps
stackedAlign q =
  $(pattern 'q "R1 ((q11) Align (qr1=R1 ((q12) Align (q2))))"
    [| do
        predicate $ $(v "q11") == $(v "q12")
        VProp (ValueVector w1) <- vectorTypeProp <$> properties $(v "q11")
        VProp (ValueVector w2) <- vectorTypeProp <$> properties $(v "q2")
  
        return $ do
            logRewrite "Redundant.Align.Stacked" q
            
            -- Aligning multiple times duplicates the left input's
            -- columns.
            let dupColsProj = map Column1 ([1..w1] ++ [1..w1] ++ (map (+ w1) [1..w2]))
            projNode <- insert $ UnOp (Project dupColsProj) $(v "qr1")

            replace q projNode |])

-- Housekeeping rule: If only columns from the left Align input are
-- referenced, remove projections on the right input.
alignedOnlyLeft :: VLRule Properties
alignedOnlyLeft q =
  $(pattern 'q "(q1) Align (Project _ (q2))"
    [| do
        -- check that only columns from the left input (outer vector)
        -- are required
        VPropPair (Just reqCols) _  <- reqColumnsProp <$> td <$> properties q
        VProp (ValueVector w)       <- vectorTypeProp <$> bu <$> properties $(v "q1")
        predicate $ all (<= w) reqCols
  
        return $ do
          logRewrite "Redundant.Align.Project" q
          void $ replaceWithNew q $ BinOp Align $(v "q1") $(v "q2") |])
          
shiftCols :: Int -> Expr1 -> Expr1
shiftCols offset expr =
    case expr of
        BinApp1 o e1 e2 -> BinApp1 o (shiftCols offset e1) (shiftCols offset e2)
        UnApp1 o e1     -> UnApp1 o (shiftCols offset e1)
        Column1 i       -> Column1 (offset + i)
        Constant1 c     -> Constant1 c
        If1 c t e       -> If1 (shiftCols offset c) (shiftCols offset t) (shiftCols offset e)

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

-- | Pull a projection on a Sort operator's input over the Sort
-- operator. This rewrite should enable the SortSimple rewrite when
-- the common source of Sort's left and right inputs is obstructed by
-- a projection.
sortProject :: VLRule ()
sortProject q =
  $(pattern 'q "R1 ((q1) Sort (Project proj (q2)))"
   [| do
       return $ do
         logRewrite "Redundant.Sort.PullProject" q
         sortNode <- insert $ BinOp Sort $(v "q1") $(v "q2")
         r1Node   <- insert $ UnOp R1 sortNode
         void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node |])

-- | Under a number of conditions, a combination of Combine and Select
-- (Restrict) operators implements a scalar conditional that can be
-- simply mapped to an 'if' expression evaluated on the input vector.
scalarConditional :: VLRule ()
scalarConditional q =
  $(pattern 'q "R1 (Combine (Project predProj (q1)) (Project thenProj (Select pred2 (q2))) (Project elseProj (Select negPred (q3))))"
    [| do
        -- All branches must work on the same input vector
        predicate $ $(v "q1") == $(v "q2") && $(v "q1") == $(v "q3")

        -- The condition projection as well as the projections for
        -- then and else branches must produce single columns.
        [predExpr] <- return $(v "predProj")
        [thenExpr] <- return $(v "thenProj")
        [elseExpr] <- return $(v "elseProj")

        -- The condition for the boolean vector must be the same as
        -- the selection condition for the then-branch.
        predicate $ predExpr == $(v "pred2")
        
        -- The selection condition must be the negated form of the
        -- then-condition.
        predicate $ (UnApp1 Not predExpr) == $(v "negPred")

        return $ do
          logRewrite "Redundant.ScalarConditional" q
          void $ replaceWithNew q $ UnOp (Project [If1 predExpr thenExpr elseExpr]) $(v "q1") |])
        
------------------------------------------------------------------------------
-- Projection pullup

-- | Pull a projection atop a Restrict operator. This rewrite mainly
-- serves to clear the way for merging of Combine/Restrict
-- combinations into scalar conditional expressions.
pullProjectRestrict :: VLRule ()
pullProjectRestrict q =
  $(pattern 'q "R1 ((Project projs (q1)) Restrict (qb))"
     [| do
          return $ do
            logRewrite "Redundant.Project.Restrict" q
            restrictNode <- insert $ BinOp Restrict $(v "q1") $(v "qb")
            r1Node       <- insert $ UnOp R1 restrictNode
            void $ replaceWithNew q $ UnOp (Project $(v "projs")) r1Node |])

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

