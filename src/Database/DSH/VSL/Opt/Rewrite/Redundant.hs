{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VSL.Opt.Rewrite.Redundant (removeRedundancy) where

import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Opt
import           Database.DSH.Common.VectorLang
import           Database.DSH.VSL.Lang
import           Database.DSH.VSL.Opt.Properties.Types
import           Database.DSH.VSL.Opt.Properties.VectorType
import           Database.DSH.VSL.Opt.Rewrite.Aggregation
import           Database.DSH.VSL.Opt.Rewrite.Common
import           Database.DSH.VSL.Opt.Rewrite.Expressions
-- import           Database.DSH.VSL.Opt.Rewrite.Window

{-# ANN module "HLint: ignore Reduce duplication" #-}

removeRedundancy :: VSLRewrite Bool
removeRedundancy =
    iteratively $ sequenceRewrites [ cleanup
                                   , applyToAll noProps redundantRules
                                   , applyToAll inferBottomUp redundantRulesBottomUp
                                   , applyToAll inferProperties redundantRulesAllProps
                                   , groupingToAggregation
                                   ]

cleanup :: VSLRewrite Bool
cleanup = iteratively $ sequenceRewrites [ optExpressions ]

redundantRules :: VSLRuleSet ()
redundantRules = [ pullProjectSort
                 , pullProjectMergeMap
                 , pullProjectUnitMap
                 , scalarConditional
                 , pushUnboxSngAlign
                 , pushUnboxSngReplicateScalar
                 ]


redundantRulesBottomUp :: VSLRuleSet BottomUpProps
redundantRulesBottomUp = [ sameInputAlign
                         , sameInputZip
                         -- , sameInputZipProject
                         -- , sameInputZipProjectLeft
                         -- , sameInputZipProjectRight
                         , zipProjectLeft
                         , alignProjectLeft
                         , zipProjectRight
                         , alignProjectRight
                         , distLiftProjectLeft
                         , distLiftProjectRight
                         , distLiftNestJoin
                         , distLiftStacked
                         , distLiftSelect
                         , alignedDistLeft
                         , alignedDistRight
                         , zipConstLeft
                         , zipConstRight
                         , alignConstLeft
                         , alignConstRight
                         , zipZipLeft
                         , alignWinLeft
                         , alignWinRight
                         , zipWinLeft
                         , zipWinRight
                         , zipWinRight2
                         , alignWinRightPush
                         , alignUnboxSngRight
                         , alignUnboxSngLeft
                         , alignUnboxDefaultRight
                         , alignUnboxDefaultLeft
                         , alignCartProdRight
                         , alignGroupJoinLeft
                         , alignGroupJoinRight
                         -- , runningAggWinBounded
                         -- , runningAggWinUnbounded
                         -- , runningAggWinUnboundedGroupJoin
                         -- , inlineWinAggrProject
                         , pullProjectNumber
                         , constDist
                         , pullProjectUnboxSngLeft
                         , pullProjectUnboxDefaultLeft
                         , pullProjectUnboxSngRight
                         , pullProjectNestJoinLeft
                         , pullProjectNestJoinRight
                         , pullProjectMaterialize
                         , pullProjectCartProductLeft
                         , pullProjectCartProductRight
                         , pullProjectGroupJoinLeft
                         , pullProjectGroupJoinRight
                         , pullProjectReplicateScalarRight
                         , selectCartProd
                         ]

redundantRulesAllProps :: VSLRuleSet Properties
redundantRulesAllProps = [ unreferencedReplicateSeg
                         , notReqNumber
                         , unboxNumber
                         ]

--------------------------------------------------------------------------------
--

unwrapConstVal :: ConstPayload -> VSLMatch p ScalarVal
unwrapConstVal (ConstPL val) = return val
unwrapConstVal  NonConstPL   = fail "not a constant"

-- | If the left input of a dist operator is constant, a normal projection
-- can be used because the Dist* operators keeps the shape of the
-- right input.
constDist :: VSLRule BottomUpProps
constDist q =
  $(dagPatMatch 'q "R1 ((q1) [ReplicateSeg | ReplicateScalar] (q2))"
    [| do
         VProp (ConstVec constCols) <- constProp <$> properties $(v "q1")
         VProp (VTDataVec w)        <- vectorTypeProp <$> properties $(v "q2")
         constVals                  <- mapM unwrapConstVal constCols

         return $ do
              logRewrite "Redundant.Const.ReplicateSeg" q
              let proj = map Constant constVals ++ map Column [1..w]
              void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

-- | If a vector is distributed over an inner vector in a segmented
-- way, check if the vector's columns are actually referenced/required
-- downstream. If not, we can remove the ReplicateSeg altogether, as the
-- shape of the inner vector is not changed by ReplicateSeg.
unreferencedReplicateSeg :: VSLRule Properties
unreferencedReplicateSeg q =
  $(dagPatMatch 'q  "R1 ((q1) ReplicateSeg (q2))"
    [| do
        VProp (Just reqCols) <- reqColumnsProp . td <$> properties q
        VProp (VTDataVec w1) <- vectorTypeProp . bu <$> properties $(v "q1")
        VProp (VTDataVec w2) <- vectorTypeProp . bu <$> properties $(v "q2")

        -- Check that only columns from the right input are required
        predicate $ all (> w1) reqCols

        return $ do
          logRewrite "Redundant.Unreferenced.ReplicateSeg" q

          -- FIXME HACKHACKHACK
          let padProj = [ Constant $ IntV 0xdeadbeef | _ <- [1..w1] ]
                        ++
                        [ Column i | i <- [1..w2] ]

          void $ replaceWithNew q $ UnOp (Project padProj) $(v "q2") |])

-- | Remove a ReplicateSeg if the outer vector is aligned with a
-- NestJoin that uses the same outer vector.
-- FIXME try to generalize to NestJoinS
distLiftNestJoin :: VSLRule BottomUpProps
distLiftNestJoin q =
  $(dagPatMatch 'q "R1 ((qo) ReplicateSeg (R1 ((qo1) NestJoin p (qi))))"
    [| do
        predicate $ $(v "qo") == $(v "qo1")

        -- Only allow the rewrite if both product inputs are flat (i.e. unit
        -- segment). This is equivalent to the old flat NestProduct rewrite.
        VProp UnitSegP <- segProp <$> properties $(v "qo1")
        VProp UnitSegP <- segProp <$> properties $(v "qi")

        w1 <- vectorWidth . vectorTypeProp <$> properties $(v "qo")
        w2 <- vectorWidth . vectorTypeProp <$> properties $(v "qi")

        return $ do
            logRewrite "Redundant.ReplicateSeg.NestJoin" q
            -- Preserve the original schema
            let proj = map Column $ [1..w1] ++ [1..w1] ++ [w1+1..w1+w2]
            prodNode <- insert $ BinOp (NestJoin $(v "p")) $(v "qo") $(v "qi")
            r1Node   <- insert $ UnOp R1 prodNode
            void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

distLiftProjectLeft :: VSLRule BottomUpProps
distLiftProjectLeft q =
  $(dagPatMatch 'q "R1 ((Project ps1 (q1)) ReplicateSeg (q2))"
    [| do
        w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
        w2 <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

        return $ do
          logRewrite "Redundant.ReplicateSeg.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let proj = $(v "ps1") ++ [ Column $ c + w1 | c <- [1 .. w2]]
          distNode <- insert $ BinOp ReplicateSeg $(v "q1") $(v "q2")
          r1Node   <- insert $ UnOp R1 distNode
          void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

distLiftProjectRight :: VSLRule BottomUpProps
distLiftProjectRight q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateSeg (Project p2 (q2)))"
    [| do
        w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

        return $ do
          logRewrite "Redundant.ReplicateSeg.Project.Right" q
          -- Take the columns from the left and the expressions from
          -- the right projection. Since expressions are applied after
          -- the zip, their column references have to be shifted.
          let proj = [Column c | c <- [1..w1]] ++ [ mapExprCols (+ w1) e | e <- $(v "p2") ]
          distNode <- insert $ BinOp ReplicateSeg $(v "q1") $(v "q2")
          r1Node   <- insert $ UnOp R1 distNode
          void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

-- If the same outer vector is propagated twice to an inner vector,
-- one ReplicateSeg can be removed. Reasoning: ReplicateSeg does not change
-- the shape of the inner vector.
distLiftStacked :: VSLRule BottomUpProps
distLiftStacked q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateSeg (r1=R1 ((q11) ReplicateSeg (q2))))"
     [| do
         predicate $ $(v "q1") == $(v "q11")
         w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
         w2 <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

         return $ do
             logRewrite "Redundant.ReplicateSeg.Stacked" q
             let proj = map Column $ [1..w1] ++ [1..w1] ++ [w1+1..w1+w2]
             void $ replaceWithNew q $ UnOp (Project proj) $(v "r1") |])

-- | Pull a selection through a ReplicateSeg. The reasoning for
-- correctness is simple: It does not matter wether an element of an
-- inner segment is removed before or after ReplicateSeg (on relational
-- level, ReplicateSeg maps to join which commutes with selection). The
-- "use case" for this rewrite is not well thought-through yet: We
-- want to push down ReplicateSeg to eliminate it or merge it with other
-- operators (e.g. ReplicateSeg.Stacked). The usual wisdom would suggest
-- to push selections down, though.
distLiftSelect :: VSLRule BottomUpProps
distLiftSelect q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateSeg (R1 (Select p (q2))))"
     [| do
         w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
         return $ do
             logRewrite "Redundant.ReplicateSeg.Select" q
             let p' = shiftExprCols w1 $(v "p")
             distNode <- insert $ BinOp ReplicateSeg $(v "q1") $(v "q2")
             distR1   <- insert $ UnOp R1 distNode
             selNode  <- insert $ UnOp (Select p') distR1
             void $ replaceWithNew q $ UnOp R1 selNode |])

-- | When a ReplicateSeg result is aligned with the right (inner) ReplicateSeg
-- input, we can eliminate the Align. Reasoning: ReplicateSeg does not
-- change the shape of the vector, only adds columns from its right
-- input.
alignedDistRight :: VSLRule BottomUpProps
alignedDistRight q =
  $(dagPatMatch 'q "(q21) Align (qr1=R1 ((q1) [ReplicateSeg | ReplicateScalar] (q22)))"
    [| do
        predicate $ $(v "q21") == $(v "q22")
        w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
        w2 <- vectorWidth . vectorTypeProp <$> properties $(v "q21")

        return $ do
            logRewrite "Redundant.Dist.Align.Right" q
            let proj = map Column $
                       [w1+1..w1+w2]
                       ++
                       [1..w1]
                       ++
                       [w1+1..w1+w2]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "qr1") |])

-- | When a ReplicateSeg result is aligned with the right (inner) ReplicateSeg
-- input, we can eliminate the Align. Reasoning: ReplicateSeg does not
-- change the shape of the vector, only adds columns from its right
-- input.
alignedDistLeft :: VSLRule BottomUpProps
alignedDistLeft q =
  $(dagPatMatch 'q "(qr1=R1 ((q1) [ReplicateSeg | ReplicateScalar] (q21))) Align (q22)"
    [| do
        predicate $ $(v "q21") == $(v "q22")
        w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
        w2 <- vectorWidth . vectorTypeProp <$> properties $(v "q21")

        return $ do
            logRewrite "Redundant.Dist.Align.Left" q
            let proj = map Column $
                       [1..w1]
                       ++
                       [w1+1..w1+w2]
                       ++
                       [w1+1..w1+w2]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "qr1") |])

--------------------------------------------------------------------------------
-- Zip and Align rewrites.

-- Note that the rewrites valid for Zip are a subset of the rewrites
-- valid for Align. In the case of Align, we statically know that both
-- inputs have the same length and can be positionally aligned without
-- discarding elements.

-- | Replace an Align operator with a projection if both inputs are the
-- same.
sameInputAlign :: VSLRule BottomUpProps
sameInputAlign q =
  $(dagPatMatch 'q "(q1) Align (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

        return $ do
          logRewrite "Redundant.Align.Self" q
          let ps = map Column [1 .. w]
          void $ replaceWithNew q $ UnOp (Project (ps ++ ps)) $(v "q1") |])

-- | Replace an Align operator with a projection if both inputs are the
-- same.
sameInputZip :: VSLRule BottomUpProps
sameInputZip q =
  $(dagPatMatch 'q "R1 ((q1) Zip (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip.Self" q
          let ps = map Column [1 .. w]
          void $ replaceWithNew q $ UnOp (Project (ps ++ ps)) $(v "q1") |])

-- sameInputZipProject :: VSLRule BottomUpProps
-- sameInputZipProject q =
--   $(dagPatMatch 'q "(Project ps1 (q1)) [Zip | Align] (Project ps2 (q2))"
--     [| do
--         predicate $ $(v "q1") == $(v "q2")

--         return $ do
--           logRewrite "Redundant.Zip/Align.Self.Project" q
--           void $ replaceWithNew q $ UnOp (Project ($(v "ps1") ++ $(v "ps2"))) $(v "q1") |])

-- sameInputZipProjectLeft :: VSLRule BottomUpProps
-- sameInputZipProjectLeft q =
--   $(dagPatMatch 'q "(Project ps1 (q1)) [Zip | Align] (q2)"
--     [| do
--         predicate $ $(v "q1") == $(v "q2")
--         w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

--         return $ do
--           logRewrite "Redundant.Zip/Align.Self.Project.Left" q
--           let proj = $(v "ps1") ++ (map Column [1..w1])
--           void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

-- sameInputZipProjectRight :: VSLRule BottomUpProps
-- sameInputZipProjectRight q =
--   $(dagPatMatch 'q "(q1) [Zip | Align] (Project ps2 (q2))"
--     [| do
--         predicate $ $(v "q1") == $(v "q2")
--         w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

--         return $ do
--           logRewrite "Redundant.Zip/Align.Self.Project.Right" q
--           let proj = (map Column [1 .. w]) ++ $(v "ps2")
--           void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

alignProjectLeft :: VSLRule BottomUpProps
alignProjectLeft q =
  $(dagPatMatch 'q "(Project ps1 (q1)) Align (q2)"
    [| do
        w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
        w2 <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

        return $ do
          logRewrite "Redundant.Align.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let proj = $(v "ps1") ++ [ Column $ c + w1 | c <- [1 .. w2]]
          alignNode <- insert $ BinOp Align $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project proj) alignNode |])

zipProjectLeft :: VSLRule BottomUpProps
zipProjectLeft q =
  $(dagPatMatch 'q "R1 ((Project ps1 (q1)) Zip (q2))"
    [| do
        w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
        w2 <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

        return $ do
          logRewrite "Redundant.Zip.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let proj = $(v "ps1") ++ [ Column $ c + w1 | c <- [1 .. w2]]
          zipNode <- insert $ BinOp Zip $(v "q1") $(v "q2")
          r1Node  <- insert $ UnOp R1 zipNode
          void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

alignProjectRight :: VSLRule BottomUpProps
alignProjectRight q =
  $(dagPatMatch 'q "(q1) Align (Project p2 (q2))"
    [| do
        w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

        return $ do
          logRewrite "Redundant.Align.Project.Right" q
          -- Take the columns from the left and the expressions from
          -- the right projection. Since expressions are applied after
          -- the zip, their column references have to be shifted.
          let proj = [Column c | c <- [1..w1]] ++ [ mapExprCols (+ w1) e | e <- $(v "p2") ]
          zipNode <- insert $ BinOp Align $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project proj) zipNode |])

zipProjectRight :: VSLRule BottomUpProps
zipProjectRight q =
  $(dagPatMatch 'q "R1 ((q1) Zip (Project p2 (q2)))"
    [| do
        w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip.Project.Right" q
          -- Take the columns from the left and the expressions from
          -- the right projection. Since expressions are applied after
          -- the zip, their column references have to be shifted.
          let proj = [Column c | c <- [1..w1]] ++ [ mapExprCols (+ w1) e | e <- $(v "p2") ]
          zipNode <- insert $ BinOp Zip $(v "q1") $(v "q2")
          r1Node  <- insert $ UnOp R1 zipNode
          void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

fromConst :: Monad m => ConstPayload -> m ScalarVal
fromConst (ConstPL val) = return val
fromConst NonConstPL    = fail "not a constant"

-- | This rewrite is valid because we statically know that both
-- vectors have the same length.
alignConstLeft :: VSLRule BottomUpProps
alignConstLeft q =
  $(dagPatMatch 'q "(q1) Align (q2)"
    [| do
        VProp (ConstVec ps) <- constProp <$> properties $(v "q1")
        w2                  <- vectorWidth . vectorTypeProp <$> properties $(v "q2")
        vals                <- mapM fromConst ps

        return $ do
            logRewrite "Redundant.Align.Constant.Left" q
            let proj = map Constant vals ++ map Column [1..w2]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

alignConstRight :: VSLRule BottomUpProps
alignConstRight q =
  $(dagPatMatch 'q "(q1) Align (q2)"
    [| do
        w1                  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
        VProp (ConstVec ps) <- constProp <$> properties $(v "q2")
        vals                <- mapM fromConst ps

        return $ do
            logRewrite "Redundant.Align.Constant.Right" q
            let proj = map Column [1..w1] ++ map Constant vals
            void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

-- | In contrast to the 'Align' version ('alignConstLeft') this rewrite is only
-- valid if we can statically determine that both input vectors have the same
-- length. If the constant vector was shorter, overhanging elements from the
-- non-constant vector would need to be discarded. In general, we can only
-- determine equal length for the special case of length one.
--
-- Since we use Zip here, we have to ensure that the constant is in the same
-- segment as the entry from the non-constant tuple. At the moment, we can
-- guarantee this only for unit-segment vectors.
zipConstLeft :: VSLRule BottomUpProps
zipConstLeft q =
  $(dagPatMatch 'q "R1 ((q1) Zip (q2))"
    [| do

        prop1               <- properties $(v "q1")
        VProp card1         <- return $ card1Prop prop1
        VProp (ConstVec ps) <- return $ constProp prop1
        VProp UnitSegP      <- return $ segProp prop1

        prop2               <- properties $(v "q2")
        VProp card2         <- return $ card1Prop prop2
        w2                  <- vectorWidth . vectorTypeProp <$> properties $(v "q2")
        VProp UnitSegP      <- return $ segProp prop2

        vals                <- mapM fromConst ps
        predicate $ card1 && card2

        return $ do
            logRewrite "Redundant.Zip.Constant.Left" q
            let proj = map Constant vals ++ map Column [1..w2]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

zipConstRight :: VSLRule BottomUpProps
zipConstRight q =
  $(dagPatMatch 'q "R1 ((q1) Zip (q2))"
    [| do
        prop1               <- properties $(v "q1")
        VProp card1         <- return $ card1Prop prop1
        w1                  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
        VProp UnitSegP      <- return $ segProp prop1

        prop2               <- properties $(v "q2")
        VProp card2         <- return $ card1Prop prop2
        VProp (ConstVec ps) <- return $ constProp prop2
        VProp UnitSegP      <- return $ segProp prop2


        vals                  <- mapM fromConst ps
        predicate $ card1 && card2

        return $ do
            logRewrite "Redundant.Zip.Constant.Right" q
            let proj = map Column [1..w1] ++ map Constant vals
            void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

zipZipLeft :: VSLRule BottomUpProps
zipZipLeft q =
  $(dagPatMatch 'q "(q1) Zip (qz=(q11) [Zip | Align] (_))"
     [| do
         predicate $ $(v "q1") == $(v "q11")

         w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
         wz <- vectorWidth . vectorTypeProp <$> properties $(v "qz")

         return $ do
             logRewrite "Redundant.Zip/Align.Zip.Left" q
             let proj = map Column $ [1..w1] ++ [1..wz]
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qz") |])

alignWinRight :: VSLRule BottomUpProps
alignWinRight q =
  $(dagPatMatch 'q "(q1) Align (qw=WinFun _ (q2))"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         w <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

         return $ do
             logRewrite "Redundant.Align.Self.Win.Right" q
             -- We get all columns from the left input. The WinAggr
             -- operator produces the input column followed by the
             -- window function result.
             let proj = map Column $ [1 .. w] ++ [1 .. w] ++ [w+1]
             -- logGeneral ("zipWinRight " ++ show proj)
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qw") |])

zipWinRight :: VSLRule BottomUpProps
zipWinRight q =
  $(dagPatMatch 'q "R1 ((q1) Zip (qw=WinFun _ (q2)))"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         w <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

         return $ do
             logRewrite "Redundant.Zip.Self.Win.Right" q
             -- We get all columns from the left input. The WinAggr
             -- operator produces the input column followed the window
             -- function result.
             let proj = map Column $ [1 .. w] ++ [1 .. w] ++ [w+1]
             -- logGeneral ("zipWinRight " ++ show proj)
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qw") |])

-- | Remove a Zip operator when the right input consists of two window
-- operators.
--
-- FIXME this should be solved properly for the general case.
zipWinRight2 :: VSLRule BottomUpProps
zipWinRight2 q =
  $(dagPatMatch 'q "R1 ((q1) Zip (qw=WinFun _ (WinFun _ (q2))))"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         w <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

         return $ do
             logRewrite "Redundant.Zip.Self.Win.Right.Double" q
             -- We get all columns from the left input. The WinAggr
             -- operator produces the input column followed the window
             -- function result.
             let proj = map Column $ [1 .. w] ++ [1 .. w] ++ [w+1, w+2]
             -- logGeneral ("zipWinRight " ++ show proj)
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qw") |])

alignWinLeft :: VSLRule BottomUpProps
alignWinLeft q =
  $(dagPatMatch 'q "(qw=WinFun _ (q1)) Align (q2)"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         w <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

         return $ do
             logRewrite "Redundant.Align.Self.Win.Left" q
             -- We get all input columns plus the window function
             -- output from the left. From the right we get all input
             -- columns.
             let proj = map Column $ [1 .. w] ++ [w+1] ++ [1 .. w]
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qw") |])

-- | If the output of a window operator is zipped with its own input, we can
-- remove the Zip operator.
zipWinLeft :: VSLRule BottomUpProps
zipWinLeft q =
  $(dagPatMatch 'q "R1 ((qw=WinFun _ (q1)) Zip (q2))"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         w <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

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

alignWinRightPush :: VSLRule BottomUpProps
alignWinRightPush q =
  $(dagPatMatch 'q "(q1) Align (WinFun args (q2))"
    [| do
        let (winFun, frameSpec) = $(v "args")
        predicate $ isPrecedingFrameSpec frameSpec
        w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

        return $ do
            logRewrite "Redundant.Align.Win.Right" q
            zipNode <- insert $ BinOp Align $(v "q1") $(v "q2")
            let winFun' = mapWinFun (mapExprCols (+ w1)) winFun
                args'   = (winFun', frameSpec)
            void $ replaceWithNew q $ UnOp (WinFun args') zipNode |])

alignGroupJoinRight :: VSLRule BottomUpProps
alignGroupJoinRight q =
  $(dagPatMatch 'q "(qo) Align (gj=(qo1) GroupJoin args (_))"
    [| do
        let (_, _, _, as) = $(v "args")
            aggCount      = length $ getNE as
        predicate $ $(v "qo") == $(v "qo1")
        w <- vectorWidth . vectorTypeProp <$> properties $(v "qo")

        return $ do
            logRewrite "Redundant.Align.GroupJoin.Right" q
            -- In the result, replicate the columns from the outer
            -- vector to keep the schema intact.
            let proj = map Column $ [1..w] ++ [1..w+aggCount]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "gj") |])

alignGroupJoinLeft :: VSLRule BottomUpProps
alignGroupJoinLeft q =
  $(dagPatMatch 'q "(gj=(qo1) GroupJoin args (_)) Align (qo)"
    [| do
        let (_, _, _, as) = $(v "args")
            aggCount      = length $ getNE as
        predicate $ $(v "qo") == $(v "qo1")
        w <- vectorWidth . vectorTypeProp <$> properties $(v "qo")

        return $ do
            logRewrite "Redundant.Align.GroupJoin.Left" q
            -- In the result, replicate the columns from the outer
            -- vector to keep the schema intact.
            let proj = map Column $ [1..w+aggCount] ++ [1..w]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "gj") |])

-- | If the right (outer) input of Unbox is a Number operator and the
-- number output is not required, eliminate it from the outer
-- input. This is correct because Number does not change the vertical
-- shape of the vector.
--
-- The motivation is to eliminate zip operators that align with the
-- unboxed block. By removing Number from the Unbox input, we hope to
-- achieve that the outer input is the same one as the zip input so
-- that we can remove the zip.
--
-- For an example, see the bestProfit query (AQuery examples).
--
-- FIXME This could be extended to all operators that do not modify
-- the vertical shape.
unboxNumber :: VSLRule Properties
unboxNumber q =
  $(dagPatMatch 'q "R1 ((Number (qo)) UnboxSng (qi))"
    [| do
        VProp (Just reqCols) <- reqColumnsProp . td <$> properties q
        VProp (VTDataVec wo) <- vectorTypeProp . bu <$> properties $(v "qo")
        VProp (VTDataVec wi) <- vectorTypeProp . bu <$> properties $(v "qi")
        predicate $ (wo+1) `notElem` reqCols

        return $ do
            logRewrite "Redundant.Unbox.Number" q
            -- FIXME HACKHACKHACK We have to insert a dummy column in
            -- place of the number column to avoid destroying column
            -- indexes.
            let proj = map Column [1..wo]
                       ++ [Constant $ IntV 0xdeadbeef]
                       ++ map Column [wo+1..wi+wo]
            unboxNode <- insert $ BinOp UnboxSng $(v "qo") $(v "qi")
            r1Node    <- insert $ UnOp R1 unboxNode
            void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

-- | If singleton scalar elements in an inner vector (with singleton
-- segments) are unboxed using an outer vector and then aligned with
-- the same outer vector, we can eliminate the align, because the
-- positional alignment is implicitly performed by the UnboxSng
-- operator. We exploit the fact that UnboxSng is only a
-- specialized join which nevertheless produces payload columns from
-- both inputs.
alignUnboxSngRight :: VSLRule BottomUpProps
alignUnboxSngRight q =
  $(dagPatMatch 'q "(q11) Align (qu=R1 ((q12) UnboxSng (q2)))"
     [| do
         predicate $ $(v "q11") == $(v "q12")

         leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q11")
         rightWidth <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

         return $ do
             logRewrite "Redundant.Align.UnboxSng.Right" q


             -- Keep the original schema intact by duplicating columns
             -- from the left input (UnboxSng produces columns from
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

-- | See Align.UnboxSng.Right
alignUnboxSngLeft :: VSLRule BottomUpProps
alignUnboxSngLeft q =
  $(dagPatMatch 'q "(qu=R1 ((q11) UnboxSng (q2))) Align (q12)"
     [| do
         predicate $ $(v "q11") == $(v "q12")

         leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q11")
         rightWidth <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

         return $ do
             logRewrite "Redundant.Align.UnboxSng.Left" q


             -- Keep the original schema intact by duplicating columns
             -- from the left input (UnboxSng produces columns from
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

-- | If singleton scalar elements in an inner vector (with singleton
-- segments) are unboxed using an outer vector and then aligned with
-- the same outer vector, we can eliminate the align, because the
-- positional alignment is implicitly performed by the UnboxSng
-- operator. We exploit the fact that UnboxSng is only a
-- specialized join which nevertheless produces payload columns from
-- both inputs.
alignUnboxDefaultRight :: VSLRule BottomUpProps
alignUnboxDefaultRight q =
  $(dagPatMatch 'q "(q11) Align (qu=R1 ((q12) UnboxDefault _ (q2)))"
     [| do
         predicate $ $(v "q11") == $(v "q12")

         leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q11")
         rightWidth <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

         return $ do
             logRewrite "Redundant.Align.UnboxDefault.Right" q


             -- Keep the original schema intact by duplicating columns
             -- from the left input (UnboxDefault produces columns from
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

-- | See Align.UnboxDefault.Right
alignUnboxDefaultLeft :: VSLRule BottomUpProps
alignUnboxDefaultLeft q =
  $(dagPatMatch 'q "(qu=R1 ((q11) UnboxDefault _ (q2))) Align (q12)"
     [| do
         predicate $ $(v "q11") == $(v "q12")

         leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q11")
         rightWidth <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

         return $ do
             logRewrite "Redundant.Align.UnboxDefault.Left" q


             -- Keep the original schema intact by duplicating columns
             -- from the left input (UnboxDefault produces columns from
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
alignCartProdRight :: VSLRule BottomUpProps
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
scalarConditional :: VSLRule ()
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
        predicate $ UnApp (SUBoolOp Not) predExpr == $(v "negPred")

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

pullProjectGroupJoinLeft :: VSLRule BottomUpProps
pullProjectGroupJoinLeft q =
  $(dagPatMatch 'q "(Project proj (q1)) GroupJoin args (q2)"
    [| do
        let (l1, l2, p, as)  = $(v "args")
            aggCount = length $ getNE as
        leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
        rightWidth <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

        return $ do
            logRewrite "Redundant.Project.GroupJoin.Left" q
            let proj'     = $(v "proj") ++ map Column [leftWidth+1..leftWidth+aggCount]
                p'        = inlineJoinPredLeft (zip [1..] $(v "proj")) p
                rightCols = [leftWidth+1 .. leftWidth + rightWidth]
                env       = zip [1..] ($(v "proj") ++ map Column rightCols)
                as'       = NE $ mapAggrFun (mergeExpr env) <$> getNE as

            joinNode <- insert $ BinOp (GroupJoin (l1, l2, p', as')) $(v "q1") $(v "q2")
            void $ replaceWithNew q $ UnOp (Project proj') joinNode |])

pullProjectGroupJoinRight :: VSLRule BottomUpProps
pullProjectGroupJoinRight q =
  $(dagPatMatch 'q "(q1) GroupJoin args (Project proj (q2))"
    [| do
        let (l1, l2, p, as) = $(v "args")
        leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

        return $ do
            logRewrite "Redundant.Project.GroupJoin.Right" q
            let p'        = inlineJoinPredRight (zip [1..] $(v "proj")) p
                leftCols  = [1..leftWidth]
                -- Shift column names in the projection expressions to account
                -- for the name shift due to the join.
                proj'     = map (shiftExprCols leftWidth) $(v "proj")
                env       = zip [1..] (map Column leftCols ++ proj')
                as'        = NE $ mapAggrFun (mergeExpr env) <$> getNE as

            void $ replaceWithNew q $ BinOp (GroupJoin (l1, l2, p', as')) $(v "q1") $(v "q2") |])

pullProjectMaterialize :: VSLRule BottomUpProps
pullProjectMaterialize q =
  $(dagPatMatch 'q "R1 ((q1) Materialize (Project p (q2)))"
    [| return $ do
            logRewrite "Redundant.Project.Materialize" q
            repNode <- insert $ BinOp Materialize $(v "q1") $(v "q2")
            r1Node  <- replaceWithNew q $ UnOp R1 repNode
            void $ replaceWithNew q $ UnOp (Project $(v "p")) r1Node

            -- FIXME relink R2 parents
            |])

pullProjectNestJoinLeft :: VSLRule BottomUpProps
pullProjectNestJoinLeft q =
  $(dagPatMatch 'q "R1 ((Project proj (q1)) NestJoin args (q2))"
    [| do
        let (l1, l2, p) = $(v "args")
        leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
        rightWidth <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

        return $ do
            logRewrite "Redundant.Project.NestJoin.Left" q
            let proj' = $(v "proj") ++ map Column [leftWidth + 1 .. leftWidth + rightWidth]
                p'    = inlineJoinPredLeft (zip [1..] $(v "proj")) p

            joinNode <- insert $ BinOp (NestJoin (l1, l2, p')) $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 joinNode
            void $ replaceWithNew q $ UnOp (Project proj') r1Node

            -- FIXME relink R2 and R3 parents
            |])

pullProjectNestJoinRight :: VSLRule BottomUpProps
pullProjectNestJoinRight q =
  $(dagPatMatch 'q "R1 ((q1) NestJoin args (Project proj (q2)))"
    [| do
        let (l1, l2, p) = $(v "args")
        leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

        return $ do
            logRewrite "Redundant.Project.NestJoin.Right" q
            let proj' = map Column [1..leftWidth] ++ map (shiftExprCols leftWidth) $(v "proj")
                p'    = inlineJoinPredRight (zip [1..] $(v "proj")) p

            joinNode <- insert $ BinOp (NestJoin (l1, l2, p')) $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 joinNode
            void $ replaceWithNew q $ UnOp (Project proj') r1Node

            -- FIXME relink R2 and R3 parents
            |])

pullProjectCartProductLeft :: VSLRule BottomUpProps
pullProjectCartProductLeft q =
  $(dagPatMatch 'q "R1 ((Project proj (q1)) CartProduct (q2))"
    [| do
        leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
        rightWidth <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

        return $ do
            logRewrite "Redundant.Project.CartProduct.Left" q
            let proj' = $(v "proj") ++ map Column [leftWidth + 1 .. leftWidth + rightWidth]

            prodNode <- insert $ BinOp CartProduct $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 prodNode
            void $ replaceWithNew q $ UnOp (Project proj') r1Node

            -- FIXME relink R2 and R3 parents
            |])

pullProjectCartProductRight :: VSLRule BottomUpProps
pullProjectCartProductRight q =
  $(dagPatMatch 'q "R1 ((q1) CartProduct (Project proj (q2)))"
    [| do
        leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

        return $ do
            logRewrite "Redundant.Project.CartProduct.Right" q
            let proj' = map Column [1..leftWidth] ++ map (shiftExprCols leftWidth) $(v "proj")

            prodNode <- insert $ BinOp CartProduct $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 prodNode
            void $ replaceWithNew q $ UnOp (Project proj') r1Node

            -- FIXME relink R2 and R3 parents
            |])


pullProjectNumber :: VSLRule BottomUpProps
pullProjectNumber q =
  $(dagPatMatch 'q "Number (Project proj (q1))"
    [| do
         w <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

         return $ do
             logRewrite "Redundant.Project.Number" q

             -- We have to preserve the numbering column in the
             -- pulled-up projection.
             let proj' = $(v "proj") ++ [Column $ w + 1]
             numberNode <- insert $ UnOp Number $(v "q1")
             void $ replaceWithNew q $ UnOp (Project proj') numberNode |])

pullProjectSort :: VSLRule ()
pullProjectSort q =
  $(dagPatMatch 'q "R1 (Sort ses (Project ps (q1)))"
    [| return $ do
           logRewrite "Redundant.Project.Sort" q
           let env = zip [1..] $(v "ps")
           let ses' = map (mergeExpr env) $(v "ses")
           sortNode <- insert $ UnOp (Sort ses') $(v "q1")
           r1Node   <- insert (UnOp R1 sortNode)
           void $ replaceWithNew q $ UnOp (Project $(v "ps")) r1Node |])

pullProjectUnboxDefaultLeft :: VSLRule BottomUpProps
pullProjectUnboxDefaultLeft q =
  $(dagPatMatch 'q "R1 ((Project proj (q1)) UnboxDefault vs (q2))"
    [| do
         leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
         rightWidth <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

         return $ do
           logRewrite "Redundant.Project.UnboxSng" q

           -- Employ projection expressions on top of the unboxing
           -- operator, add right input columns.
           let proj' = $(v "proj") ++ map Column [ leftWidth + 1 .. leftWidth + rightWidth ]
           unboxNode <- insert $ BinOp (UnboxDefault $(v "vs")) $(v "q1") $(v "q2")
           r1Node    <- insert $ UnOp R1 unboxNode

           void $ replaceWithNew q $ UnOp (Project proj') r1Node |])


pullProjectUnboxSngLeft :: VSLRule BottomUpProps
pullProjectUnboxSngLeft q =
  $(dagPatMatch 'q "R1 ((Project proj (q1)) UnboxSng (q2))"
    [| do
         leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
         rightWidth <- vectorWidth . vectorTypeProp <$> properties $(v "q2")

         return $ do
           logRewrite "Redundant.Project.UnboxSng" q

           -- Employ projection expressions on top of the unboxing
           -- operator, add right input columns.
           let proj' = $(v "proj") ++ map Column [ leftWidth + 1 .. leftWidth + rightWidth ]
           unboxNode <- insert $ BinOp UnboxSng $(v "q1") $(v "q2")
           r1Node    <- insert $ UnOp R1 unboxNode

           void $ replaceWithNew q $ UnOp (Project proj') r1Node |])

pullProjectUnboxSngRight :: VSLRule BottomUpProps
pullProjectUnboxSngRight q =
  $(dagPatMatch 'q "R1 ((q1) UnboxSng (Project proj (q2)))"
    [| do
         leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

         return $ do
           logRewrite "Redundant.Project.UnboxSng" q

           -- Preserve left input columns on top of the unboxing
           -- operator and add right input expressions with shifted
           -- columns.
           let proj' = map Column [1..leftWidth]
                       ++
                       [ mapExprCols (+ leftWidth) e | e <- $(v "proj") ]

           unboxNode <- insert $ BinOp UnboxSng $(v "q1") $(v "q2")
           r1Node    <- insert $ UnOp R1 unboxNode

           void $ replaceWithNew q $ UnOp (Project proj') r1Node |])

pullProjectReplicateScalarRight :: VSLRule BottomUpProps
pullProjectReplicateScalarRight q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateScalar (Project p (q2)))"
    [| do
         leftWidth  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

         return $ do
           logRewrite "Redundant.Project.ReplicateScalar" q
           let p' = map Column [1..leftWidth]
                    ++
                    [ mapExprCols (+ leftWidth) e | e <- $(v "p") ]
           distNode <- insert $ BinOp ReplicateScalar $(v "q1") $(v "q2")
           r1Node   <- insert $ UnOp R1 distNode
           void $ replaceWithNew q $ UnOp (Project p') r1Node |])

pullProjectMergeMap :: VSLRule ()
pullProjectMergeMap q =
  $(dagPatMatch 'q "MergeMap (Project _ (q1))"
    [| return $ do
           logRewrite "Redundant.Project.MergeMap" q
           void $ replaceWithNew q $ UnOp MergeMap $(v "q1") |])

pullProjectUnitMap :: VSLRule ()
pullProjectUnitMap q =
  $(dagPatMatch 'q "UnitMap (Project _ (q1))"
    [| return $ do
           logRewrite "Redundant.Project.UnitMap" q
           void $ replaceWithNew q $ UnOp UnitMap $(v "q1") |])

--------------------------------------------------------------------------------
-- Rewrites that deal with nested structures and propagation vectors.

--------------------------------------------------------------------------------
-- Eliminating operators whose output is not required

notReqNumber :: VSLRule Properties
notReqNumber q =
  $(dagPatMatch 'q "Number (q1)"
    [| do
        w <- vectorWidth . vectorTypeProp . bu <$> properties $(v "q1")
        VProp (Just reqCols) <- reqColumnsProp . td <$> properties $(v "q")

        -- The number output in column w + 1 must not be required
        predicate $ all (<= w) reqCols

        return $ do
          logRewrite "Redundant.Req.Number" q
          -- Add a dummy column instead of the number output to keep
          -- column references intact.
          let proj = map Column [1..w] ++ [Constant $ IntV 0xdeadbeef]
          void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

--------------------------------------------------------------------------------
-- Classical relational algebra rewrites

-- | Merge a selection that refers to both sides of a cartesian
-- product operators' inputs into a join.
selectCartProd :: VSLRule BottomUpProps
selectCartProd q =
  $(dagPatMatch 'q "R1 (Select p (R1 ((q1) CartProduct (q2))))"
    [| do
        wl <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
        BinApp (SBRelOp op) (Column lc) (Column rc) <- return $(v "p")

        -- The left operand column has to be from the left input, the
        -- right operand from the right input.
        predicate $ lc <= wl
        predicate $ rc > wl

        return $ do
            logRewrite "Redundant.Relational.Join" q
            let joinPred = singlePred $ JoinConjunct (Column lc) op (Column $ rc - wl)
            joinNode <- insert $ BinOp (ThetaJoin (Direct, Direct, joinPred)) $(v "q1") $(v "q2")
            void $ replaceWithNew q $ UnOp R1 joinNode |])

--------------------------------------------------------------------------------
-- Normalization rules for segment aggregation

-- | Apply a singleton unbox operator before an align operator. By unboxing
-- early, we hope to be able to eliminate unboxing (e.g. by combining it with an
-- AggrSeg and Group operator).
--
-- Note: We could either push into the left or right align input. For no good
-- reason, we choose the right side. When we deal with a self-align, this will
-- not matter. There might however be plans where the left side would make more
-- sense and we might get stuck.
pushUnboxSngAlign :: VSLRule ()
pushUnboxSngAlign q =
  $(dagPatMatch 'q "R1 (((q1) Align (q2)) UnboxSng (q3))"
    [| return $ do
           logRewrite "Redundant.UnboxSng.Push.Align" q
           unboxNode <- insert $ BinOp UnboxSng $(v "q2") $(v "q3")
           r1Node    <- insert $ UnOp R1 unboxNode
           void $ replaceWithNew q $ BinOp Align $(v "q1") r1Node |])

-- | Unbox singletons early, namely before distributing another singleton.
--
-- Note: the same comment as for pushUnboxSngAlign applies.
pushUnboxSngReplicateScalar :: VSLRule ()
pushUnboxSngReplicateScalar q =
  $(dagPatMatch 'q "R1 ((R1 ((q1) ReplicateScalar (q2))) UnboxSng (q3))"
    [| return $ do
           logRewrite "Redundant.UnboxSng.Push.ReplicateScalar" q
           unboxNode <- insert $ BinOp UnboxSng $(v "q2") $(v "q3")
           r1Node    <- insert $ UnOp R1 unboxNode
           distNode  <- insert $ BinOp ReplicateScalar $(v "q1") r1Node
           void $ replaceWithNew q $ UnOp R1 distNode |])
