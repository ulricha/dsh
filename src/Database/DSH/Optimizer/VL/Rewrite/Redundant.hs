{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Rewrite.Redundant (removeRedundancy) where

import           Control.Applicative
import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Lang
import           Database.DSH.Impossible
import           Database.DSH.Optimizer.Common.Rewrite
import           Database.DSH.Optimizer.VL.Properties.Types
import           Database.DSH.Optimizer.VL.Properties.VectorType
import           Database.DSH.Optimizer.VL.Rewrite.Common
import           Database.DSH.Optimizer.VL.Rewrite.Expressions
import           Database.DSH.Optimizer.VL.Rewrite.Aggregation
import           Database.DSH.Optimizer.VL.Rewrite.Window
import           Database.DSH.VL.Lang

removeRedundancy :: VLRewrite Bool
removeRedundancy =
    iteratively $ sequenceRewrites [ cleanup
                                   , applyToAll noProps redundantRules
                                   , applyToAll inferBottomUp redundantRulesBottomUp
                                   , applyToAll inferProperties redundantRulesAllProps
                                   , groupingToAggregation
                                   ]

cleanup :: VLRewrite Bool
cleanup = iteratively $ sequenceRewrites [ optExpressions ]

redundantRules :: VLRuleSet ()
redundantRules = [ mergeProjectRestrict
                 , scalarRestrict
                 , simpleSort
                 , sortProject
                 , pullProjectPropRename
                 , pullProjectPropReorder
                 , pullProjectRestrict
                 , pullProjectSelectPos1S
                 , pullProjectPropFilter
                 , pullProjectUnboxRename
                 , scalarConditional
                 ]

redundantRulesBottomUp :: VLRuleSet BottomUpProps
redundantRulesBottomUp = [ distPrimConstant
                         , distDescConstant
                         , sameInputZip
                         , sameInputZipProject
                         , sameInputZipProjectLeft
                         , sameInputZipProjectRight
                         , zipProjectLeft
                         , zipProjectRight
                         , alignParents
                         , selectConstPos
                         , selectConstPosS
                         , completeSort
                         , restrictZip
                         , zipConstLeft
                         , zipConstRight
                         , zipZipLeft
                         , zipWinLeft
                         , zipWinRight
                         , zipWinRightPush
                         -- , stackedAlign
                         , propProductCard1Right
                         , runningAggWin
                         , inlineWinAggrProject
                         , restrictWinFun
                         , pullProjectNumber
                         , constAlign
                         ]

redundantRulesAllProps :: VLRuleSet Properties
redundantRulesAllProps = [ unreferencedAlign
                         , alignedOnlyLeft
                         , firstValueWin
                         , notReqNumber
                         ]

--------------------------------------------------------------------------------
-- Restrict rewrites

-- | Support rewrite: If a WinFun operator /adds/ columns to the
-- restrict input that are used in the condition, push it down into
-- the left Restrict input. This helps to turn Restricts into Selects.
restrictWinFun :: VLRule BottomUpProps
restrictWinFun q =
  $(dagPatMatch 'q "R1 ((q1) Restrict p (qw=WinFun _ (q2)))"
    [| do
         predicate $ $(v "q1") == $(v "q2")
         w <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
         return $ do
           logRewrite "Redundant.Restrict.WinFun" q

           restrictNode <- insert $ BinOp (Restrict $(v "p")) $(v "qw") $(v "qw")
           r1Node       <- insert $ UnOp R1 restrictNode

           -- Remove the window function output.
           let proj = map Column [1..w]
           void $ replaceWithNew q $ UnOp (Project proj) r1Node |])
           


mergeProjectRestrict :: VLRule ()
mergeProjectRestrict q =
  $(dagPatMatch 'q "(q1) Restrict p (Project es (q2))"
    [| do
        return $ do
          logRewrite "Redundant.Restrict.Project" q
          let env = zip [1..] $(v "es")
              p'  = mergeExpr env $(v "p")
          void $ replaceWithNew q $ BinOp (Restrict p') $(v "q1") $(v "q2") |])

-- | If the left input of a Restrict operator that builds the
-- filtering vector is just a simple scalar expression, a scalar
-- Select can be used instead.
scalarRestrict :: VLRule ()
scalarRestrict q =
  $(dagPatMatch 'q "R1 (qr=(q1) Restrict p (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.Restrict.Scalar" q
          selectNode <- insert $ UnOp (Select $(v "p")) $(v "q1")
          void $ replaceWithNew q $ UnOp R1 selectNode

          r2Parents <- lookupR2Parents $(v "qr")

          -- If there are any R2 nodes linking to the original
          -- Restrict operator (i.e. there are inner vectors to which
          -- changes must be propagated), they have to be rewired to
          -- the new Select operator.
          when (not $ null r2Parents) $ do
            qr2' <- insert $ UnOp R2 selectNode
            mapM_ (\qr2 -> replace qr2 qr2') r2Parents |])

-- | If the vector that is to be filtered by Restrict (left input) is
-- combined with the filter criteria to go into the Restrict
-- predicate, we might just turn the Restrict into a Select. Columns
-- from the left are already present after the zip and re-joining them
-- after selection is not necessary.
restrictZip :: VLRule BottomUpProps
restrictZip q =
  $(dagPatMatch 'q "R1 (qr=(q1) Restrict p (qz=(q2) Zip (_)))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
        
        return $ do
          logRewrite "Redundant.Restrict.Zip" q
          let proj = [ Column c | c <- [1..w]]

          selNode <- insert $ UnOp (Select $(v "p")) $(v "qz")
          r1Node <- insert $ UnOp R1 selNode
          void $ replaceWithNew q $ UnOp (Project proj) r1Node

          r2Parents <- lookupR2Parents $(v "qr")

          -- If there are any R2 nodes linking to the original
          -- Restrict operator (i.e. there are inner vectors to which
          -- changes must be propagated), they have to be rewired to
          -- the new Select operator.
          when (not $ null r2Parents) $ do
            qr2' <- insert $ UnOp R2 selNode
            mapM_ (\qr2 -> replace qr2 qr2') r2Parents |])

--------------------------------------------------------------------------------
-- 



-- | Replace a DistPrim operator with a projection if its value input
-- is constant.
distPrimConstant :: VLRule BottomUpProps
distPrimConstant q =
  $(dagPatMatch 'q "R1 ((qp) DistPrim (qv))"
    [| do
        qvProps <- properties $(v "qp")

        constProjs <- case constProp qvProps of
          VProp (DBVConst _ cols) -> mapM (constVal Constant) cols
          _                       -> fail "no match"

        return $ do
          logRewrite "Redundant.DistPrim.Constant" q
          void $ replaceWithNew q $ UnOp (Project constProjs) $(v "qv") |])

-- | Replace a DistDesc operator with a projection if its value input
-- is constant and consists of only one tuple.
distDescConstant :: VLRule BottomUpProps
distDescConstant q =
  $(dagPatMatch 'q "R1 ((qv) DistDesc (qd))"
    [| do
        pv <- properties $(v "qv")
        VProp True <- return $ card1Prop pv

        VProp (DBVConst _ cols) <- return $ constProp pv
        constProjs              <- mapM (constVal Constant) cols

        return $ do
          logRewrite "Redundant.DistDesc.Constant" q
          void $ replaceWithNew q $ UnOp (Project constProjs) $(v "qd") |])

unwrapConstVal :: ConstPayload -> VLMatch p VLVal
unwrapConstVal (ConstPL val) = return val
unwrapConstVal  NonConstPL   = fail "not a constant"

-- | If the left input of an align is constant, a normal projection
-- can be used because the Align operator keeps the shape of the right
-- input.
constAlign :: VLRule BottomUpProps
constAlign q =
  $(dagPatMatch 'q "R1 ((q1) Align (q2))"
    [| do 
         VProp (DBVConst _ constCols) <- constProp <$> properties $(v "q1")
         VProp (ValueVector w)        <- vectorTypeProp <$> properties $(v "q2")
         constVals                    <- mapM unwrapConstVal constCols
         
         return $ do 
              logRewrite "Redundant.Const.Align" q
              let proj = map Constant constVals
                         ++
                         [ Column $ c + length constVals | c <- [1..w]]
              void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])
       

-- | If a vector is distributed over an inner vector in a segmented
-- way, check if the vector's columns are actually referenced/required
-- downstream. If not, we can remove the DistSeg altogether, as the
-- shape of the inner vector is not changed by DistSeg.
unreferencedAlign :: VLRule Properties
unreferencedAlign q =
  $(dagPatMatch 'q  "R1 ((q1) Align (q2))"
    [| do
        VProp (Just reqCols)   <- reqColumnsProp <$> td <$> properties q
        VProp (ValueVector w1) <- vectorTypeProp <$> bu <$> properties $(v "q1")
        VProp (ValueVector w2) <- vectorTypeProp <$> bu <$> properties $(v "q2")

        -- Check that only columns from the right input are required
        predicate $ all (> w1) reqCols

        return $ do
          logRewrite "Redundant.Unreferenced.Align" q

          -- FIXME HACKHACKHACK
          let padProj = [ Constant $ VLInt 0xdeadbeef | _ <- [1..w1] ]
                        ++
                        [ Column i | i <- [1..w2] ]

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
  $(dagPatMatch 'q "R1 ((q1) Align (q2))"
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
             let origColsProj = [ Column $ w1 + i | i <- [1 .. w2] ]
             projNode <- insert $ UnOp (Project origColsProj) q

             -- Then, re-link all parents of the right Align input to
             -- the projection.
             forM_ nonAlignParents $ \p -> replaceChild p $(v "q2") projNode |])

-- | If an outer vector is aligned multiple times with some inner
-- vector (i.e. stacked Align operators with the same left input), one
-- Align is sufficient.
stackedAlign :: VLRule BottomUpProps
stackedAlign q =
  $(dagPatMatch 'q "R1 ((q11) Align (qr1=R1 ((q12) Align (q2))))"
    [| do
        predicate $ $(v "q11") == $(v "q12")
        VProp (ValueVector w1) <- vectorTypeProp <$> properties $(v "q11")
        VProp (ValueVector w2) <- vectorTypeProp <$> properties $(v "q2")

        return $ do
            logRewrite "Redundant.Align.Stacked" q

            -- Aligning multiple times duplicates the left input's
            -- columns.
            let dupColsProj = map Column ([1..w1] ++ [1..w1] ++ (map (+ w1) [1..w2]))
            projNode <- insert $ UnOp (Project dupColsProj) $(v "qr1")

            replace q projNode |])

-- Housekeeping rule: If only columns from the left Align input are
-- referenced, remove projections on the right input.
alignedOnlyLeft :: VLRule Properties
alignedOnlyLeft q =
  $(dagPatMatch 'q "(q1) Align (Project _ (q2))"
    [| do
        -- check that only columns from the left input (outer vector)
        -- are required
        VPropPair (Just reqCols) _  <- reqColumnsProp <$> td <$> properties q
        VProp (ValueVector w)       <- vectorTypeProp <$> bu <$> properties $(v "q1")
        predicate $ all (<= w) reqCols

        return $ do
          logRewrite "Redundant.Align.Project" q
          void $ replaceWithNew q $ BinOp Align $(v "q1") $(v "q2") |])

--------------------------------------------------------------------------------
-- Zip rewrites

-- | Replace a Zip operator with a projection if both inputs are the
-- same.
sameInputZip :: VLRule BottomUpProps
sameInputZip q =
  $(dagPatMatch 'q "(q1) Zip (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip.Self" q
          let ps = map Column [1 .. w]
          void $ replaceWithNew q $ UnOp (Project (ps ++ ps)) $(v "q1") |])

sameInputZipProject :: VLRule BottomUpProps
sameInputZipProject q =
  $(dagPatMatch 'q "(Project ps1 (q1)) Zip (Project ps2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.Zip.Self.Project" q
          void $ replaceWithNew q $ UnOp (Project ($(v "ps1") ++ $(v "ps2"))) $(v "q1") |])

sameInputZipProjectLeft :: VLRule BottomUpProps
sameInputZipProjectLeft q =
  $(dagPatMatch 'q "(Project ps1 (q1)) Zip (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip.Self.Project.Left" q
          let proj = $(v "ps1") ++ (map Column [1..w1])
          void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

sameInputZipProjectRight :: VLRule BottomUpProps
sameInputZipProjectRight q =
  $(dagPatMatch 'q "(q1) Zip (Project ps2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip.Self.Project.Right" q
          let proj = (map Column [1 .. w]) ++ $(v "ps2")
          void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

zipProjectLeft :: VLRule BottomUpProps
zipProjectLeft q =
  $(dagPatMatch 'q "(Project ps1 (q1)) Zip (q2)"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q2")

        return $ do
          logRewrite "Redundant.Zip.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let proj = $(v "ps1") ++ [ Column $ c + w1 | c <- [1 .. w2]]
          zipNode <- insert $ BinOp Zip $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project proj) zipNode |])

zipProjectRight :: VLRule BottomUpProps
zipProjectRight q =
  $(dagPatMatch 'q "(q1) Zip (Project p2 (q2))"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip.Project.Right" q
          -- Take the columns from the left and the expressions from
          -- the right projection. Since expressions are applied after
          -- the zip, their column references have to be shifted.
          let proj = [Column c | c <- [1..w1]] ++ [ mapExprCols (+ w1) e | e <- $(v "p2") ]
          zipNode <- insert $ BinOp Zip $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project proj) zipNode |])

fromConst :: Monad m => ConstPayload -> m VLVal
fromConst (ConstPL val) = return val
fromConst NonConstPL    = fail "not a constant"

zipConstLeft :: VLRule BottomUpProps
zipConstLeft q =
  $(dagPatMatch 'q "(q1) Zip (q2)"
    [| do
        prop1                 <- properties $(v "q1")
        VProp card1           <- return $ card1Prop prop1
        VProp (DBVConst _ ps) <- return $ constProp prop1

        prop2                 <- properties $(v "q2")
        VProp card2           <- return $ card1Prop prop2
        w2                    <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")

        vals                  <- mapM fromConst ps
        predicate $ card1 && card2

        return $ do
            logRewrite "Redundant.Zip.Constant.Left" q
            let proj = map Constant vals ++ map Column [1..w2]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

zipConstRight :: VLRule BottomUpProps
zipConstRight q =
  $(dagPatMatch 'q "(q1) Zip (q2)"
    [| do
        prop1                 <- properties $(v "q1")
        VProp card1           <- return $ card1Prop prop1
        w1                    <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

        prop2                 <- properties $(v "q2")
        VProp card2           <- return $ card1Prop prop2
        VProp (DBVConst _ ps) <- return $ constProp prop2


        vals                  <- mapM fromConst ps
        predicate $ card1 && card2

        return $ do
            logRewrite "Redundant.Zip.Constant.Right" q
            let proj = map Column [1..w1] ++ map Constant vals
            void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

zipZipLeft :: VLRule BottomUpProps
zipZipLeft q =
  $(dagPatMatch 'q "(q1) Zip (qz=(q11) Zip (_))"
     [| do
         predicate $ $(v "q1") == $(v "q11")

         w1 <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
         wz <- vectorWidth <$> vectorTypeProp <$> properties $(v "qz")
        
         return $ do
             logRewrite "Redundant.Zip.Zip.Left" q
             let proj = map Column $ [1..w1] ++ [1..wz]
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qz") |])

zipWinRight :: VLRule BottomUpProps
zipWinRight q =
  $(dagPatMatch 'q "(q1) Zip (qw=WinFun _ (q2))"
     [| do
         predicate $ $(v "q1") == $(v "q2")
         
         w <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
         
         return $ do
             logRewrite "Redundant.Zip.Self.Win.Right" q
             -- We get all columns from the left input. The WinAggr
             -- operator produces the input column followed the window
             -- function result.
             let proj = map Column $ [1 .. w] ++ [1 .. w] ++ [w+1]
             logGeneral ("zipWinRight " ++ show proj)
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qw") |])

zipWinLeft :: VLRule BottomUpProps
zipWinLeft q =
  $(dagPatMatch 'q "(qw=WinFun _ (q1)) Zip (q2)"
     [| do
         predicate $ $(v "q1") == $(v "q2")
         
         w <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
         
         return $ do
             logRewrite "Redundant.Zip.Self.Win.Left" q
             -- We get all input columns plus the window function
             -- output from the left. From the right we get all input
             -- columns.
             let proj = map Column $ [1 .. w] ++ [w+1] ++ [1 .. w]
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qw") |])

isPrecedingFrameSpec :: FrameSpec -> Bool
isPrecedingFrameSpec fs =
    case fs of
        FAllPreceding -> True
        FNPreceding _ -> True

zipWinRightPush :: VLRule BottomUpProps
zipWinRightPush q =
  $(dagPatMatch 'q "(q1) Zip (WinFun args (q2))"
    [| do
        let (winFun, frameSpec) = $(v "args")
        predicate $ isPrecedingFrameSpec frameSpec
        w1 <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

        return $ do
            logRewrite "Redundant.Zip.Win.Right" q
            zipNode <- insert $ BinOp Zip $(v "q1") $(v "q2")
            let winFun' = mapWinFun (mapExprCols (\c -> c + w1)) winFun
                args'   = (winFun', frameSpec)
            void $ replaceWithNew q $ UnOp (WinFun args') zipNode |])

--------------------------------------------------------------------------------
-- Specialization of sorting

-- | Employ a specialized operator if the sorting criteria are simply
-- a selection of columns from the input vector.
simpleSort :: VLRule ()
simpleSort q =
  $(dagPatMatch 'q "(Project ps (q1)) SortS (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.Sort.Scalar" q
          void $ replaceWithNew q $ UnOp (SortScalarS $(v "ps")) $(v "q1") |])

-- | Special case: a vector is sorted by all its item columns.
completeSort :: VLRule BottomUpProps
completeSort q =
  $(dagPatMatch 'q "(q1) SortS (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        VProp (ValueVector w) <- vectorTypeProp <$> properties $(v "q1")

        return $ do
          logRewrite "Redundant.Sort.Complete" q
          let sortProj = map Column [1..w]
          void $ replaceWithNew q $ UnOp (SortScalarS sortProj) $(v "q1") |])

-- | Pull a projection on a Sort operator's input over the Sort
-- operator. This rewrite should enable the SortScalarS rewrite when
-- the common source of Sort's left and right inputs is obstructed by
-- a projection.
sortProject :: VLRule ()
sortProject q =
  $(dagPatMatch 'q "R1 ((q1) SortS (Project proj (q2)))"
   [| do
       return $ do
         logRewrite "Redundant.Sort.PullProject" q
         sortNode <- insert $ BinOp SortS $(v "q1") $(v "q2")
         r1Node   <- insert $ UnOp R1 sortNode
         void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node |])

--------------------------------------------------------------------------------
-- Scalar conditionals

-- | Under a number of conditions, a combination of Combine and Select
-- (Restrict) operators implements a scalar conditional that can be
-- simply mapped to an 'if' expression evaluated on the input vector.
scalarConditional :: VLRule ()
scalarConditional q =
  $(dagPatMatch 'q "R1 (Combine (Project predProj (q1)) (Project thenProj (R1 (Select pred2 (q2)))) (Project elseProj (R1 (Select negPred (q3)))))"
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
        predicate $ (UnApp (SUBoolOp Not) predExpr) == $(v "negPred")

        return $ do
          logRewrite "Redundant.ScalarConditional" q
          void $ replaceWithNew q $ UnOp (Project [If predExpr thenExpr elseExpr]) $(v "q1") |])

------------------------------------------------------------------------------
-- Projection pullup

pullProjectNumber :: VLRule BottomUpProps
pullProjectNumber q =
  $(dagPatMatch 'q "Number (Project proj (q1))"
    [| do
         w <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

         return $ do
             logRewrite "Redundant.Project.Number" q

             -- We have to preserve the numbering column in the
             -- pulled-up projection.
             let proj' = $(v "proj") ++ [Column $ w + 1]
             numberNode <- insert $ UnOp Number $(v "q1")
             void $ replaceWithNew q $ UnOp (Project proj') numberNode |])

-- | Pull a projection atop a Restrict operator. This rewrite mainly
-- serves to clear the way for merging of Combine/Restrict
-- combinations into scalar conditional expressions.
pullProjectRestrict :: VLRule ()
pullProjectRestrict q =
  $(dagPatMatch 'q "R1 ((Project projs (q1)) Restrict p (qb))"
     [| do
          return $ do
            logRewrite "Redundant.Project.Restrict" q
            restrictNode <- insert $ BinOp (Restrict $(v "p")) $(v "q1") $(v "qb")
            r1Node       <- insert $ UnOp R1 restrictNode
            void $ replaceWithNew q $ UnOp (Project $(v "projs")) r1Node |])

-- Motivation: In order to eliminate or pull up sorting operations in
-- VL rewrites or subsequent stages, payload columns which might
-- induce sort order should be available as long as possible. We
-- assume that the cost of having unrequired columns around is
-- negligible (best case: column store).

pullProjectPropRename :: VLRule ()
pullProjectPropRename q =
  $(dagPatMatch 'q "(qp) PropRename (Project proj (qv))"
    [| do
         return $ do
           logRewrite "Redundant.Project.PropRename" q
           renameNode <- insert $ BinOp PropRename $(v "qp") $(v "qv")
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) renameNode |])

pullProjectPropReorder :: VLRule ()
pullProjectPropReorder q =
  $(dagPatMatch 'q "R1 ((qp) PropReorder (Project proj (qv)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.Reorder" q
           reorderNode <- insert $ BinOp PropReorder $(v "qp") $(v "qv")
           r1Node      <- insert $ UnOp R1 reorderNode
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node |])

pullProjectSelectPos1S :: VLRule ()
pullProjectSelectPos1S q =
  $(dagPatMatch 'q "R1 (qs=SelectPos1S args (Project proj (q1)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.SelectPos1S" q
           selectNode  <- insert $ UnOp (SelectPos1S $(v "args")) $(v "q1")
           r1Node      <- insert $ UnOp R1 selectNode
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node |])

pullProjectPropFilter :: VLRule ()
pullProjectPropFilter q =
  $(dagPatMatch 'q "R1 ((q1) PropFilter (Project proj (q2)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.PropFilter" q
           filterNode <- insert $ BinOp PropFilter $(v "q1") $(v "q2")
           r1Node     <- insert $ UnOp R1 filterNode
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node |])

pullProjectUnboxRename :: VLRule ()
pullProjectUnboxRename q =
  $(dagPatMatch 'q "UnboxRename (Project _ (q1))"
    [| do
         return $ do
           logRewrite "Redundant.Project.UnboxRename" q
           void $ replaceWithNew q $ UnOp UnboxRename $(v "q1") |])

--------------------------------------------------------------------------------
-- Positional selection on constants

selectConstPos :: VLRule BottomUpProps
selectConstPos q =
  $(dagPatMatch 'q "(q1) SelectPos op (qp)"
    [| do
         VProp (DBVConst _ constCols) <- constProp <$> properties $(v "qp")
         pos <- case constCols of
                    [ConstPL (VLInt p)] -> return p
                    [NonConstPL]        -> fail "no match"
                    _                   -> $impossible

         return $ do
           logRewrite "Redundant.SelectPos.Constant" q
           void $ replaceWithNew q $ UnOp (SelectPos1 ($(v "op"), pos)) $(v "q1") |])

selectConstPosS :: VLRule BottomUpProps
selectConstPosS q =
  $(dagPatMatch 'q "(q1) SelectPosS op (qp)"
    [| do
         VProp (DBVConst _ constCols) <- constProp <$> properties $(v "qp")
         pos <- case constCols of
                    [ConstPL (VLInt p)] -> return p
                    [NonConstPL]        -> fail "no match"
                    _                   -> $impossible

         return $ do
           logRewrite "Redundant.SelectPosS.Constant" q
           void $ replaceWithNew q $ UnOp (SelectPos1S ($(v "op"), pos)) $(v "q1") |])

--------------------------------------------------------------------------------
-- Rewrites that deal with nested structures and propagation vectors.

-- | When the right input of a cartesian product has cardinality one,
-- the cardinality of the right input does not change and the
-- propagation vector for the left input is a NOOP.
propProductCard1Right :: VLRule BottomUpProps
propProductCard1Right q =
  $(dagPatMatch 'q "R1 ((R2 ((_) CartProduct (q2))) PropReorder (qi))"
    [| do
        VProp True <- card1Prop <$> properties $(v "q2")
        
        return $ do
          logRewrite "Redundant.Prop.CartProduct.Card1.Right" q
          void $ replace q $(v "qi") |])

--------------------------------------------------------------------------------
-- Eliminating operators whose output is not required

notReqNumber :: VLRule Properties
notReqNumber q =
  $(dagPatMatch 'q "Number (q1)"
    [| do
        w <- vectorWidth <$> vectorTypeProp <$> bu <$> properties $(v "q1")
        VProp (Just reqCols) <- reqColumnsProp <$> td <$> properties $(v "q")

        -- The number output in column w + 1 must not be required
        predicate $ all (<= w) reqCols

        return $ do
          logRewrite "Redundant.Req.Number" q
          -- Add a dummy column instead of the number output to keep
          -- column references intact.
          let proj = map Column [1..w] ++ [Constant $ VLInt 0xdeadbeef]
          void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])
           
