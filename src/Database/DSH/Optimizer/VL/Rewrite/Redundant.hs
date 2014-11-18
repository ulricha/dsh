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
redundantRules = [ pullProjectPropRename
                 , pullProjectPropReorder
                 , pullProjectSelectPos1S
                 , pullProjectPropFilter
                 , pullProjectUnboxRename
                 , pullProjectAggrS
                 , scalarConditional
                 ]

redundantRulesBottomUp :: VLRuleSet BottomUpProps
redundantRulesBottomUp = [ cartProdConstant
                         , sameInputZip
                         , sameInputZipProject
                         , sameInputZipProjectLeft
                         , sameInputZipProjectRight
                         , zipProjectLeft
                         , zipProjectRight
                         , distLiftParents
                         , selectConstPos
                         , selectConstPosS
                         , zipConstLeft
                         , zipConstRight
                         , alignConstLeft
                         , alignConstRight
                         , zipZipLeft
                         , zipWinLeft
                         , zipWinRight
                         , zipWinRightPush
                         , zipUnboxScalarRight
                         , zipUnboxScalarLeft
                         , alignCartProdRight
                         -- , stackedDistLift
                         , propProductCard1Right
                         , runningAggWin
                         , inlineWinAggrProject
                         , pullProjectNumber
                         , constDistLift
                         , nestJoinChain
                         , pullProjectUnboxScalarLeft
                         , pullProjectUnboxScalarRight
                         , pullProjectNestJoinLeft
                         , pullProjectNestJoinRight
                         , selectCartProd
                         ]

redundantRulesAllProps :: VLRuleSet Properties
redundantRulesAllProps = [ unreferencedDistLift
                         , distLiftedOnlyLeft
                         , firstValueWin
                         , notReqNumber
                         ]

--------------------------------------------------------------------------------
-- 

-- | Replace a 'CartProduct' operator with a projection if its right
-- input is constant and has cardinality one.
cartProdConstant :: VLRule BottomUpProps
cartProdConstant q =
  $(dagPatMatch 'q "R1 ((q1) CartProduct (q2))"
    [| do
        qvProps <- properties $(v "q2")

        VProp True              <- return $ card1Prop qvProps
        VProp (DBVConst _ cols) <- return $ constProp qvProps
        constProjs              <- mapM (constVal Constant) cols

        -- Preserve columns from the left input
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        let proj = map Column [1..w1] ++ constProjs

        return $ do
          logRewrite "Redundant.CartProduct.Constant" q
          void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

unwrapConstVal :: ConstPayload -> VLMatch p VLVal
unwrapConstVal (ConstPL val) = return val
unwrapConstVal  NonConstPL   = fail "not a constant"

-- | If the left input of an distLift is constant, a normal projection
-- can be used because the DistLift operator keeps the shape of the right
-- input.
constDistLift :: VLRule BottomUpProps
constDistLift q =
  $(dagPatMatch 'q "R1 ((q1) DistLift (q2))"
    [| do 
         VProp (DBVConst _ constCols) <- constProp <$> properties $(v "q1")
         VProp (ValueVector w)        <- vectorTypeProp <$> properties $(v "q2")
         constVals                    <- mapM unwrapConstVal constCols
         
         return $ do 
              logRewrite "Redundant.Const.DistLift" q
              let proj = map Constant constVals ++ map Column [1..w]
              void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])
       
-- | If a vector is distributed over an inner vector in a segmented
-- way, check if the vector's columns are actually referenced/required
-- downstream. If not, we can remove the DistSeg altogether, as the
-- shape of the inner vector is not changed by DistSeg.
unreferencedDistLift :: VLRule Properties
unreferencedDistLift q =
  $(dagPatMatch 'q  "R1 ((q1) DistLift (q2))"
    [| do
        VProp (Just reqCols)   <- reqColumnsProp <$> td <$> properties q
        VProp (ValueVector w1) <- vectorTypeProp <$> bu <$> properties $(v "q1")
        VProp (ValueVector w2) <- vectorTypeProp <$> bu <$> properties $(v "q2")

        -- Check that only columns from the right input are required
        predicate $ all (> w1) reqCols

        return $ do
          logRewrite "Redundant.Unreferenced.DistLift" q

          -- FIXME HACKHACKHACK
          let padProj = [ Constant $ VLInt 0xdeadbeef | _ <- [1..w1] ]
                        ++
                        [ Column i | i <- [1..w2] ]

          void $ replaceWithNew q $ UnOp (Project padProj) $(v "q2") |])

nonDistLiftOp :: AlgNode -> VLMatch p Bool
nonDistLiftOp n = do
    op <- getOperator n
    case op of
        BinOp DistLift _ _ -> return False
        _                  -> return True

-- | The DistLift operator keeps shape and columns of its right
-- input. When this right input is referenced by other operators than
-- DistLift, we can move these operators to the DistLift output.
--
-- This is beneficial if a composed expression depends on the DistLift
-- output (some lifted environment value) as well as the original
-- (inner) vector. In that case, we can rewrite things such that only
-- the DistLift operator is referenced (not its right input). In
-- consequence, the expression has only one source and can be merged
-- into a projection.
distLiftParents :: VLRule BottomUpProps
distLiftParents q =
  $(dagPatMatch 'q "R1 ((q1) DistLift (q2))"
     [| do
         parentNodes     <- getParents $(v "q2")
         nonDistLiftParents <- filterM nonDistLiftOp parentNodes
         predicate $ not $ null nonDistLiftParents

         VProp (ValueVector w1) <- vectorTypeProp <$> properties $(v "q1")
         VProp (ValueVector w2) <- vectorTypeProp <$> properties $(v "q2")

         return $ do
             logRewrite "Redundant.DistLift.Parents" q

             -- First, insert a projection on top of DistLift that leaves
             -- only the columns from DistLift's right input.
             let origColsProj = [ Column $ w1 + i | i <- [1 .. w2] ]
             projNode <- insert $ UnOp (Project origColsProj) q

             -- Then, re-link all parents of the right DistLift input to
             -- the projection.
             forM_ nonDistLiftParents $ \p -> replaceChild p $(v "q2") projNode |])

-- Housekeeping rule: If only columns from the left DistLift input are
-- referenced, remove projections on the right input.
distLiftedOnlyLeft :: VLRule Properties
distLiftedOnlyLeft q =
  $(dagPatMatch 'q "(q1) DistLift (Project _ (q2))"
    [| do
        -- check that only columns from the left input (outer vector)
        -- are required
        VPropPair (Just reqCols) _  <- reqColumnsProp <$> td <$> properties q
        VProp (ValueVector w)       <- vectorTypeProp <$> bu <$> properties $(v "q1")
        predicate $ all (<= w) reqCols

        return $ do
          logRewrite "Redundant.DistLift.Project" q
          void $ replaceWithNew q $ BinOp DistLift $(v "q1") $(v "q2") |])

--------------------------------------------------------------------------------
-- Zip and Align rewrites. 

-- Note that the rewrites valid for Zip are a subset of the rewrites
-- valid for Align. In the case of Align, we statically know that both
-- inputs have the same length and can be positionally aligned without
-- discarding elements.

-- | Replace a Zip operator with a projection if both inputs are the
-- same.
sameInputZip :: VLRule BottomUpProps
sameInputZip q =
  $(dagPatMatch 'q "(q1) [Zip | Align] (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip/Align.Self" q
          let ps = map Column [1 .. w]
          void $ replaceWithNew q $ UnOp (Project (ps ++ ps)) $(v "q1") |])

sameInputZipProject :: VLRule BottomUpProps
sameInputZipProject q =
  $(dagPatMatch 'q "(Project ps1 (q1)) [Zip | Align] (Project ps2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.Zip/Align.Self.Project" q
          void $ replaceWithNew q $ UnOp (Project ($(v "ps1") ++ $(v "ps2"))) $(v "q1") |])

sameInputZipProjectLeft :: VLRule BottomUpProps
sameInputZipProjectLeft q =
  $(dagPatMatch 'q "(Project ps1 (q1)) [Zip | Align] (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip/Align.Self.Project.Left" q
          let proj = $(v "ps1") ++ (map Column [1..w1])
          void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

sameInputZipProjectRight :: VLRule BottomUpProps
sameInputZipProjectRight q =
  $(dagPatMatch 'q "(q1) [Zip | Align] (Project ps2 (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip/Align.Self.Project.Right" q
          let proj = (map Column [1 .. w]) ++ $(v "ps2")
          void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

zipProjectLeft :: VLRule BottomUpProps
zipProjectLeft q =
  $(dagPatMatch 'q "(Project ps1 (q1)) [Zip | Align]@op (q2)"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q2")

        return $ do
          logRewrite "Redundant.Zip/Align.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let proj = $(v "ps1") ++ [ Column $ c + w1 | c <- [1 .. w2]]
          zipNode <- insert $ BinOp $(v "op") $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project proj) zipNode |])

zipProjectRight :: VLRule BottomUpProps
zipProjectRight q =
  $(dagPatMatch 'q "(q1) [Zip | Align]@op (Project p2 (q2))"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip/Align.Project.Right" q
          -- Take the columns from the left and the expressions from
          -- the right projection. Since expressions are applied after
          -- the zip, their column references have to be shifted.
          let proj = [Column c | c <- [1..w1]] ++ [ mapExprCols (+ w1) e | e <- $(v "p2") ]
          zipNode <- insert $ BinOp $(v "op") $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project proj) zipNode |])

fromConst :: Monad m => ConstPayload -> m VLVal
fromConst (ConstPL val) = return val
fromConst NonConstPL    = fail "not a constant"

-- | This rewrite is valid because we statically know that both
-- vectors have the same length.
alignConstLeft :: VLRule BottomUpProps
alignConstLeft q =
  $(dagPatMatch 'q "(q1) Align (q2)"
    [| do
        VProp (DBVConst _ ps) <- constProp <$> properties $(v "q1")
        w2                    <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")

        vals                  <- mapM fromConst ps

        return $ do
            logRewrite "Redundant.Align.Constant.Left" q
            let proj = map Constant vals ++ map Column [1..w2]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

alignConstRight :: VLRule BottomUpProps
alignConstRight q =
  $(dagPatMatch 'q "(q1) Align (q2)"
    [| do
        w1                    <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

        VProp (DBVConst _ ps) <- constProp <$> properties $(v "q2")


        vals                  <- mapM fromConst ps

        return $ do
            logRewrite "Redundant.Align.Constant.Right" q
            let proj = map Column [1..w1] ++ map Constant vals
            void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

-- | In contrast to the 'Align' version ('alignConstLeft') this
-- rewrite is only valid if we can statically determine that both
-- input vectors have the same length. If the constant vector was
-- shorter, overhanging elements from the non-constant vector would
-- need to be discarded. In general, we can only determine equal
-- length for the special case of length one.
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
  $(dagPatMatch 'q "(q1) Zip (qz=(q11) [Zip | Align] (_))"
     [| do
         predicate $ $(v "q1") == $(v "q11")

         w1 <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
         wz <- vectorWidth <$> vectorTypeProp <$> properties $(v "qz")
        
         return $ do
             logRewrite "Redundant.Zip/Align.Zip.Left" q
             let proj = map Column $ [1..w1] ++ [1..wz]
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qz") |])

zipWinRight :: VLRule BottomUpProps
zipWinRight q =
  $(dagPatMatch 'q "(q1) [Zip | Align] (qw=WinFun _ (q2))"
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
  $(dagPatMatch 'q "(qw=WinFun _ (q1)) [Zip | Align] (q2)"
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

-- | If singleton scalar elements in an inner vector (with singleton
-- segments) are unboxed using an outer vector and then zipped with
-- the same outer vector, we can eliminate the zip, because the
-- positional alignment is implicitly performed by the UnboxScalar
-- operator. We exploit the fact that UnboxScalar is only a
-- specialized join which nevertheless produces payload columns from
-- both inputs.
zipUnboxScalarRight :: VLRule BottomUpProps
zipUnboxScalarRight q = 
  $(dagPatMatch 'q "(q11) Align (qu=(q12) UnboxScalar (q2))"
     [| do
         predicate $ $(v "q11") == $(v "q12")

         leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q11")
         rightWidth <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")

         return $ do
             logRewrite "Redundant.Align.UnboxScalar.Right" q
             

             -- Keep the original schema intact by duplicating columns
             -- from the left input (UnboxScalar produces columns from
             -- its left and right inputs).
             let outputCols = -- Two times the left input columns
                              [1..leftWidth] ++ [1..leftWidth] 
                              -- Followed by the right input columns
                              ++ [ leftWidth+1..rightWidth+leftWidth ]
                 proj       = map Column outputCols

             -- Keep only the unboxing operator, together with a
             -- projection that keeps the original output schema
             -- intact.
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qu") |])

-- | See Align.UnboxScalar.Right
zipUnboxScalarLeft :: VLRule BottomUpProps
zipUnboxScalarLeft q = 
  $(dagPatMatch 'q "(qu=(q11) UnboxScalar (q2)) Align (q12)"
     [| do
         predicate $ $(v "q11") == $(v "q12")

         leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q11")
         rightWidth <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")

         return $ do
             logRewrite "Redundant.Align.UnboxScalar.Left" q
             

             -- Keep the original schema intact by duplicating columns
             -- from the left input (UnboxScalar produces columns from
             -- its left and right inputs).
             let outputCols = -- The left (outer) columns
                              [1..leftWidth]
                              -- Followed by the right (inner) input columns
                              ++ [ leftWidth+1..rightWidth+leftWidth ]
                              -- Followed by the left (outer columns) again
                              -- (originally produced by Align)
                              ++ [1..leftWidth]
                 proj       = map Column outputCols

             -- Keep only the unboxing operator, together with a
             -- projection that keeps the original output schema
             -- intact.
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qu") |])

-- | A CartProduct output is aligned with some other vector. If one of
-- the CartProduct inputs has cardinality one, the other CartProduct
-- input determines the length of the result vector. From the original
-- structure we can derive that 'q11' and the CartProduct result are
-- aligned. Consequentially, 'q11 and 'q12' (the left CartProduct
-- input) must be aligned as well.
alignCartProdRight :: VLRule BottomUpProps
alignCartProdRight q =
  $(dagPatMatch 'q "(q11) Align (R1 ((q12) CartProduct (q2)))"
    [| do
        VProp True <- card1Prop <$> properties $(v "q2")
        return $ do
            logRewrite "Redundant.Align.CartProduct.Card1.Right" q
            alignNode <- insert $ BinOp Align $(v "q11") $(v "q12")
            prodNode  <- insert $ BinOp CartProduct alignNode $(v "q2")
            void $ replaceWithNew q $ UnOp R1 prodNode |])

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

inlineJoinPredLeft :: [(DBCol, Expr)] -> JoinPredicate Expr -> JoinPredicate Expr
inlineJoinPredLeft env (JoinPred conjs) = JoinPred $ fmap inlineLeft conjs
  where
    inlineLeft :: JoinConjunct Expr -> JoinConjunct Expr
    inlineLeft (JoinConjunct le op re) = JoinConjunct (mergeExpr env le) op re

inlineJoinPredRight :: [(DBCol, Expr)] -> JoinPredicate Expr -> JoinPredicate Expr
inlineJoinPredRight env (JoinPred conjs) = JoinPred $ fmap inlineRight conjs
  where
    inlineRight :: JoinConjunct Expr -> JoinConjunct Expr
    inlineRight (JoinConjunct le op re) = JoinConjunct le op (mergeExpr env re)

pullProjectNestJoinLeft :: VLRule BottomUpProps
pullProjectNestJoinLeft q =
  $(dagPatMatch 'q "R1 ((Project proj (q1)) NestJoin p (q2))"
    [| do
        leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
        rightWidth <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")

        return $ do
            logRewrite "Redundant.Project.NestJoin.Left" q
            let proj' = $(v "proj") ++ map Column [leftWidth + 1 .. leftWidth + rightWidth]
                p'    = inlineJoinPredLeft (zip [1..] $(v "proj")) $(v "p")

            joinNode <- insert $ BinOp (NestJoin p') $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 joinNode
            void $ replaceWithNew q $ UnOp (Project proj') r1Node

            -- FIXME relink R2 and R3 parents 
            |])

pullProjectNestJoinRight :: VLRule BottomUpProps
pullProjectNestJoinRight q =
  $(dagPatMatch 'q "R1 ((q1) NestJoin p (Project proj (q2)))"
    [| do
        leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

        return $ do
            logRewrite "Redundant.Project.NestJoin.Right" q
            let proj' = map Column [1..leftWidth] ++ map (shiftExprCols leftWidth) $(v "proj")
                p'    = inlineJoinPredRight (zip [1..] $(v "proj")) $(v "p")

            joinNode <- insert $ BinOp (NestJoin p') $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 joinNode
            void $ replaceWithNew q $ UnOp (Project proj') r1Node

            -- FIXME relink R2 and R3 parents 
            |])
        

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

pullProjectUnboxScalarLeft :: VLRule BottomUpProps
pullProjectUnboxScalarLeft q =
  $(dagPatMatch 'q "(Project proj (q1)) UnboxScalar (q2)"
    [| do 
         leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
         rightWidth <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")

         return $ do
           logRewrite "Redundant.Project.UnboxScalar" q

           -- Employ projection expressions on top of the unboxing
           -- operator, add right input columns.
           let proj' = $(v "proj") ++ map Column [ leftWidth + 1 .. leftWidth + rightWidth ]
           unboxNode <- insert $ BinOp UnboxScalar $(v "q1") $(v "q2")

           void $ replaceWithNew q $ UnOp (Project proj') unboxNode |])

pullProjectUnboxScalarRight :: VLRule BottomUpProps
pullProjectUnboxScalarRight q =
  $(dagPatMatch 'q "(q1) UnboxScalar (Project proj (q2))"
    [| do 
         leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

         return $ do
           logRewrite "Redundant.Project.UnboxScalar" q

           -- Preserve left input columns on top of the unboxing
           -- operator and add right input expressions with shifted
           -- columns.
           let proj' = map Column [1..leftWidth]
                       ++
                       [ mapExprCols (+ leftWidth) e | e <- $(v "proj") ]

           unboxNode <- insert $ BinOp UnboxScalar $(v "q1") $(v "q2")

           void $ replaceWithNew q $ UnOp (Project proj') unboxNode |])
    
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

-- | Any projections on the left input of AggrS are irrelevant, as
-- only the segment information are required from the vector.
pullProjectAggrS :: VLRule ()
pullProjectAggrS q =
  $(dagPatMatch 'q "(Project _ (q1)) AggrS args (q2)"
    [| do
        return $ do
            logRewrite "Redundant.Project.AggrS" q
            void $ replaceWithNew q $ BinOp (AggrS $(v "args")) $(v "q1") $(v "q2") |])

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

-- | Turn a right-deep nestjoin tree into a left-deep one.
-- 
-- A comprehension of the form
-- @
-- [ [ [ e x y z | z <- zs, p2 y z ]
--   | y <- ys
--   , p1 x y
--   ]
-- | x <- xs
-- ]
-- @
-- 
-- is first rewritten into a right-deep chain of nestjoins: 'xs △ (ys △ zs)'. 
-- Bottom-up compilation of this expression to VL (vectorization) results in 
-- a rather awkward plan, though: The inner nestjoin is computed independent
-- of values of 'x'. The join result is then re-shaped using the propagation
-- vector from the nestjoin of the outer relations 'xs' and 'ys'. This pattern
-- is problematic for multiple reasons: PropReorder is an expensive operation as 
-- it involves re-ordering semantically, leading to a hard-to-eliminate rownum.
-- On the plan level, we do not get a left- or right-deep join tree of thetajoins,
-- but two independent joins between the two pairs of input relations whose results
-- are connected using an additional join (PropReorder). This means that the two
-- base joins will be executed on the full base tables, without being able to profit
-- from a reduced cardinality in one of the join results.
-- 
-- NestJoin does not exhibit useful algebraic properties, most notably it is neither
-- associate nor commutative. It turns out however that we can turn the pattern
-- described above into a proper left-deep sequence of nestjoins if we consider
-- the flat (vectorized) representation. The output of 'xs △ ys' is nestjoined
-- with the innermost input 'zs'. This gives us exactly the representation of
-- the nested output that we need. Semantically, 'zs' is not joined with all
-- tuples in 'ys', but only with those that survive the (outer) join with 'xs'. 
-- As usual, a proper join tree should give the engine the freedom to re-arrange 
-- the joins and drive them in a pipelined manner.
nestJoinChain :: VLRule BottomUpProps
nestJoinChain q =
  $(dagPatMatch 'q "R1 ((R3 (lj=(xs) NestJoin _ (ys))) PropReorder (R1 ((ys1) NestJoin p (zs))))"
   [| do
       xsWidth <- vectorWidth <$> vectorTypeProp <$> properties $(v "xs")
       ysWidth <- vectorWidth <$> vectorTypeProp <$> properties $(v "ys")
       zsWidth <- vectorWidth <$> vectorTypeProp <$> properties $(v "zs")

       predicate $ $(v "ys") == $(v "ys1")
       return $ do
         logRewrite "Redundant.Prop.NestJoinChain" q


         let innermostCols = map Column [ xsWidth + 1 .. xsWidth + ysWidth + zsWidth ]
  
             -- As the left input of the top nestjoin now includes the
             -- columns from xs, we have to shift column references in
             -- the left predicate side.
             JoinPred conjs = $(v "p")
             p' = JoinPred $ fmap (shiftJoinPredCols xsWidth 0) conjs

         -- The R1 node on the left nest join might already exist, but
         -- we simply rely on hash consing.
         leftJoinR1  <- insert $ UnOp R1 $(v "lj")
         rightJoin   <- insert $ BinOp (NestJoin p') leftJoinR1 $(v "zs")
         rightJoinR1 <- insert $ UnOp R1 rightJoin
  
         -- Because the original produced only the columns of ys and
         -- zs in the PropReorder output, we have to remove the xs
         -- columns from the top NestJoin.
         void $ replaceWithNew q $ UnOp (Project innermostCols) rightJoinR1 |])

shiftJoinPredCols :: Int -> Int -> JoinConjunct Expr -> JoinConjunct Expr
shiftJoinPredCols leftOffset rightOffset (JoinConjunct leftExpr op rightExpr) =
    JoinConjunct (shiftExprCols leftOffset leftExpr) op (shiftExprCols rightOffset rightExpr)

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

--------------------------------------------------------------------------------
-- Classical relational algebra rewrites

-- | Merge a selection that refers to both sides of a cartesian
-- product operators' inputs into a join.
selectCartProd :: VLRule BottomUpProps
selectCartProd q =
  $(dagPatMatch 'q "R1 (Select p (R1 ((q1) CartProduct (q2))))"
    [| do
        wl <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
        BinApp (SBRelOp op) (Column lc) (Column rc)  <- return $(v "p")
  
        -- The left operand column has to be from the left input, the
        -- right operand from the right input.
        predicate $ lc <= wl
        predicate $ rc > wl

        return $ do
            logRewrite "Redundant.Relational.Join" q
            let joinPred = singlePred $ JoinConjunct (Column lc) op (Column $ rc - wl)
            joinNode <- insert $ BinOp (ThetaJoin joinPred) $(v "q1") $(v "q2")
            void $ replaceWithNew q $ UnOp R1 joinNode |])
