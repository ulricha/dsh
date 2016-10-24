{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VSL.Opt.Rewrite.Redundant (removeRedundancy) where

import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Opt
import           Database.DSH.Common.VectorLang
import           Database.DSH.VSL.Lang
import           Database.DSH.VSL.Opt.Properties.Types
-- import           Database.DSH.VSL.Opt.Properties.VectorType
import           Database.DSH.VSL.Opt.Rewrite.Aggregation
import           Database.DSH.VSL.Opt.Rewrite.Common
import           Database.DSH.VSL.Opt.Rewrite.Expressions
-- import           Database.DSH.VSL.Opt.Rewrite.Window

{-# ANN module "HLint: ignore Reduce duplication" #-}

removeRedundancy :: VSLRewrite TExpr TExpr Bool
removeRedundancy =
    iteratively $ sequenceRewrites [ cleanup
                                   , applyToAll noProps redundantRules
                                   , applyToAll inferBottomUp redundantRulesBottomUp
                                   , applyToAll inferProperties redundantRulesAllProps
                                   , groupingToAggregation
                                   ]

cleanup :: VSLRewrite TExpr TExpr Bool
cleanup = iteratively $ sequenceRewrites [ optExpressions ]

redundantRules :: VSLRuleSet TExpr TExpr ()
redundantRules = [ pullProjectSort
                 , pullProjectMergeMap
                 , pullProjectUnitMap
                 -- , scalarConditional
                 , pushUnboxSngAlign
                 , pushUnboxSngReplicateScalar
                 , pullNumberReplicateSeg
                 , sameInputAlign
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
                 , distLiftStacked
                 -- , distLiftSelect
                 , alignedDistLeft
                 , alignedDistRight
                 -- , zipConstLeft
                 -- , zipConstRight
                 -- , alignConstLeft
                 -- , alignConstRight
                 , zipZipLeft
                 , alignWinLeft
                 , alignWinRight
                 , zipWinLeft
                 , zipWinRight
                 -- , zipWinRight2
                 , alignWinRightPush
                 , alignUnboxSngRight
                 , alignUnboxSngLeft
                 , alignUnboxDefaultRight
                 , alignUnboxDefaultLeft
                 , alignGroupJoinLeft
                 , alignGroupJoinRight
                         -- , runningAggWinBounded
                         -- , runningAggWinUnbounded
                         -- , runningAggWinUnboundedGroupJoin
                         -- , inlineWinAggrProject
                 , pullProjectNumber
                 -- , constDist
                 , pullProjectUnboxSngLeft
                 , pullProjectUnboxDefaultLeft
                 , pullProjectUnboxSngRight
                 , pullProjectNestJoinLeft
                 , pullProjectNestJoinRight
                 , pullProjectCartProductLeft
                 , pullProjectCartProductRight
                 , pullProjectGroupJoinLeft
                 , pullProjectGroupJoinRight
                 , pullProjectReplicateScalarRight
                 , selectCartProd
                 , pullNumberAlignLeft
                 , pullNumberAlignRight
                 ]


redundantRulesBottomUp :: VSLRuleSet TExpr TExpr BottomUpProps
redundantRulesBottomUp = [ pullProjectMaterialize
                         , distLiftNestJoin
                         , alignCartProdRight
                         ]

redundantRulesAllProps :: VSLRuleSet TExpr TExpr Properties
redundantRulesAllProps = [ -- unreferencedReplicateSeg
                         -- , notReqNumber
                         -- , unboxNumber
                         ]

--------------------------------------------------------------------------------
--

-- unwrapConstVal :: ConstPayload -> VSLMatch p ScalarVal
-- unwrapConstVal (ConstPL val) = return val
-- unwrapConstVal  NonConstPL   = fail "not a constant"

-- -- | If the left input of a dist operator is constant, a normal projection
-- -- can be used because the Dist* operators keeps the shape of the
-- -- right input.
-- constDist ::VSLRule TExpr TExpr BottomUpProps
-- constDist q =
--   $(dagPatMatch 'q "R1 ((q1) [ReplicateSeg | ReplicateScalar] (q2))"
--     [| do
--          VProp (ConstVec constCols) <- constProp <$> properties $(v "q1")
--          VProp (VTDataVec w)        <- vectorTypeProp <$> properties $(v "q2")
--          constVals                  <- mapM unwrapConstVal constCols

--          return $ do
--               logRewrite "Redundant.Const.ReplicateSeg" q
--               let proj = map Constant constVals ++ map Column [1..w]
--               void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

-- -- | If a vector is distributed over an inner vector in a segmented
-- -- way, check if the vector's columns are actually referenced/required
-- -- downstream. If not, we can remove the ReplicateSeg altogether, as the
-- -- shape of the inner vector is not changed by ReplicateSeg.
-- unreferencedReplicateSeg ::VSLRule TExpr TExpr Properties
-- unreferencedReplicateSeg q =
--   $(dagPatMatch 'q  "R1 ((q1) ReplicateSeg (q2))"
--     [| do
--         VProp (Just reqCols) <- reqColumnsProp . td <$> properties q
--         VProp (VTDataVec w1) <- vectorTypeProp . bu <$> properties $(v "q1")
--         VProp (VTDataVec w2) <- vectorTypeProp . bu <$> properties $(v "q2")

--         -- Check that only columns from the right input are required
--         predicate $ all (> w1) reqCols

--         return $ do
--           logRewrite "Redundant.Unreferenced.ReplicateSeg" q

--           -- FIXME HACKHACKHACK
--           let padProj = [ Constant $ IntV 0xdeadbeef | _ <- [1..w1] ]
--                         ++
--                         [ Column i | i <- [1..w2] ]

--           void $ replaceWithNew q $ UnOp (Project padProj) $(v "q2") |])

-- | Remove a ReplicateSeg if the outer vector is aligned with a
-- NestJoin that uses the same outer vector.
-- FIXME try to generalize to NestJoinS
distLiftNestJoin ::VSLRule TExpr TExpr BottomUpProps
distLiftNestJoin q =
  $(dagPatMatch 'q "R1 ((qo) ReplicateSeg (R1 ((qo1) NestJoin p (qi))))"
    [| do
        predicate $ $(v "qo") == $(v "qo1")

        -- Only allow the rewrite if both product inputs are flat (i.e. unit
        -- segment). This is equivalent to the old flat NestProduct rewrite.
        VProp UnitSegP <- segProp <$> properties $(v "qo1")
        VProp UnitSegP <- segProp <$> properties $(v "qi")

        return $ do
            logRewrite "Redundant.ReplicateSeg.NestJoin" q
            -- Preserve the original schema
            let e = VMkTuple [ VTupElem First VInput
                             , VInput
                             ]
            prodNode <- insert $ BinOp (NestJoin $(v "p")) $(v "qo") $(v "qi")
            r1Node   <- insert $ UnOp R1 prodNode
            void $ replaceWithNew q $ UnOp (Project e) r1Node |])

distLiftProjectLeft ::VSLRule TExpr TExpr ()
distLiftProjectLeft q =
  $(dagPatMatch 'q "R1 ((Project e (q1)) ReplicateSeg (q2))"
    [| do
        return $ do
          logRewrite "Redundant.ReplicateSeg.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let e' = appExprFst $(v "e")
          distNode <- insert $ BinOp ReplicateSeg $(v "q1") $(v "q2")
          r1Node   <- insert $ UnOp R1 distNode
          void $ replaceWithNew q $ UnOp (Project e') r1Node |])

distLiftProjectRight ::VSLRule TExpr TExpr ()
distLiftProjectRight q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateSeg (Project e (q2)))"
    [| do
        return $ do
          logRewrite "Redundant.ReplicateSeg.Project.Right" q
          let e' = appExprSnd $(v "e")
          distNode <- insert $ BinOp ReplicateSeg $(v "q1") $(v "q2")
          r1Node   <- insert $ UnOp R1 distNode
          void $ replaceWithNew q $ UnOp (Project e') r1Node |])

-- If the same outer vector is propagated twice to an inner vector, one
-- ReplicateSeg can be removed. Reasoning: ReplicateSeg does not change the
-- shape of the inner vector.
distLiftStacked ::VSLRule TExpr TExpr ()
distLiftStacked q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateSeg (r1=R1 ((q11) ReplicateSeg (_))))"
     [| do
         predicate $ $(v "q1") == $(v "q11")

         return $ do
             logRewrite "Redundant.ReplicateSeg.Stacked" q
             let e = VMkTuple [ VTupElem First VInput
                              , VMkTuple [ VTupElem First VInput
                                         , VTupElem (Next First) VInput
                                         ]
                              ]
             void $ replaceWithNew q $ UnOp (Project e) $(v "r1") |])

-- | Pull a selection through a ReplicateSeg. The reasoning for
-- correctness is simple: It does not matter wether an element of an
-- inner segment is removed before or after ReplicateSeg (on relational
-- level, ReplicateSeg maps to join which commutes with selection). The
-- "use case" for this rewrite is not well thought-through yet: We
-- want to push down ReplicateSeg to eliminate it or merge it with other
-- operators (e.g. ReplicateSeg.Stacked). The usual wisdom would suggest
-- to push selections down, though.
--
-- FIXME this rewrite is on rather shaky ground semantically.
-- distLiftSelect ::VSLRule TExpr TExpr BottomUpProps
-- distLiftSelect q =
--   $(dagPatMatch 'q "R1 ((q1) ReplicateSeg (R1 (Select p (q2))))"
--      [| do
--          w1 <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
--          return $ do
--              logRewrite "Redundant.ReplicateSeg.Select" q
--              let p' = shiftExprCols w1 $(v "p")
--              distNode <- insert $ BinOp ReplicateSeg $(v "q1") $(v "q2")
--              distR1   <- insert $ UnOp R1 distNode
--              selNode  <- insert $ UnOp (Select p') distR1
--              void $ replaceWithNew q $ UnOp R1 selNode |])

-- | When a ReplicateSeg result is aligned with the right (inner) ReplicateSeg
-- input, we can eliminate the Align. Reasoning: ReplicateSeg does not
-- change the shape of the vector, only adds columns from its right
-- input.
alignedDistRight ::VSLRule TExpr TExpr ()
alignedDistRight q =
  $(dagPatMatch 'q "(q21) Align (qr1=R1 ((_) [ReplicateSeg | ReplicateScalar] (q22)))"
    [| do
        predicate $ $(v "q21") == $(v "q22")

        return $ do
            logRewrite "Redundant.Dist.Align.Right" q
            let e = VMkTuple [ VTupElem (Next First) VInput
                             , VInput
                             ]
            void $ replaceWithNew q $ UnOp (Project e) $(v "qr1") |])

-- | When a ReplicateSeg result is aligned with the right (inner) ReplicateSeg
-- input, we can eliminate the Align. Reasoning: ReplicateSeg does not
-- change the shape of the vector, only adds columns from its right
-- input.
alignedDistLeft ::VSLRule TExpr TExpr ()
alignedDistLeft q =
  $(dagPatMatch 'q "(qr1=R1 ((_) [ReplicateSeg | ReplicateScalar] (q21))) Align (q22)"
    [| do
        predicate $ $(v "q21") == $(v "q22")

        return $ do
            logRewrite "Redundant.Dist.Align.Left" q
            let e = VMkTuple [ VInput
                             , VTupElem (Next First) VInput
                             ]
            void $ replaceWithNew q $ UnOp (Project e) $(v "qr1") |])

--------------------------------------------------------------------------------
-- Zip and Align rewrites.

-- Note that the rewrites valid for Zip are a subset of the rewrites
-- valid for Align. In the case of Align, we statically know that both
-- inputs have the same length and can be positionally aligned without
-- discarding elements.

-- | Replace an Align operator with a projection if both inputs are the
-- same.
sameInputAlign ::VSLRule TExpr TExpr ()
sameInputAlign q =
  $(dagPatMatch 'q "(q1) Align (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.Align.Self" q
          let e = VMkTuple [VInput, VInput]
          void $ replaceWithNew q $ UnOp (Project e) $(v "q1") |])

-- | Replace an Align operator with a projection if both inputs are the
-- same.
sameInputZip ::VSLRule TExpr TExpr ()
sameInputZip q =
  $(dagPatMatch 'q "R1 ((q1) Zip (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Redundant.Zip.Self" q
          let e = VMkTuple [VInput, VInput]
          void $ replaceWithNew q $ UnOp (Project e) $(v "q1") |])

-- sameInputZipProject ::VSLRule TExpr TExpr BottomUpProps
-- sameInputZipProject q =
--   $(dagPatMatch 'q "(Project ps1 (q1)) [Zip | Align] (Project ps2 (q2))"
--     [| do
--         predicate $ $(v "q1") == $(v "q2")

--         return $ do
--           logRewrite "Redundant.Zip/Align.Self.Project" q
--           void $ replaceWithNew q $ UnOp (Project ($(v "ps1") ++ $(v "ps2"))) $(v "q1") |])

-- sameInputZipProjectLeft ::VSLRule TExpr TExpr BottomUpProps
-- sameInputZipProjectLeft q =
--   $(dagPatMatch 'q "(Project ps1 (q1)) [Zip | Align] (q2)"
--     [| do
--         predicate $ $(v "q1") == $(v "q2")
--         w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

--         return $ do
--           logRewrite "Redundant.Zip/Align.Self.Project.Left" q
--           let proj = $(v "ps1") ++ (map Column [1..w1])
--           void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

-- sameInputZipProjectRight ::VSLRule TExpr TExpr BottomUpProps
-- sameInputZipProjectRight q =
--   $(dagPatMatch 'q "(q1) [Zip | Align] (Project ps2 (q2))"
--     [| do
--         predicate $ $(v "q1") == $(v "q2")
--         w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

--         return $ do
--           logRewrite "Redundant.Zip/Align.Self.Project.Right" q
--           let proj = (map Column [1 .. w]) ++ $(v "ps2")
--           void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

alignProjectLeft ::VSLRule TExpr TExpr ()
alignProjectLeft q =
  $(dagPatMatch 'q "(Project e (q1)) Align (q2)"
    [| do
        return $ do
          logRewrite "Redundant.Align.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let e' = appExprFst $(v "e")
          alignNode <- insert $ BinOp Align $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project e') alignNode |])

zipProjectLeft ::VSLRule TExpr TExpr ()
zipProjectLeft q =
  $(dagPatMatch 'q "R1 ((Project e (q1)) Zip (q2))"
    [| do
        return $ do
          logRewrite "Redundant.Zip.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let e' = appExprFst $(v "e")
          zipNode <- insert $ BinOp Zip $(v "q1") $(v "q2")
          r1Node  <- insert $ UnOp R1 zipNode
          void $ replaceWithNew q $ UnOp (Project e') r1Node |])

alignProjectRight ::VSLRule TExpr TExpr ()
alignProjectRight q =
  $(dagPatMatch 'q "(q1) Align (Project e (q2))"
    [| do
        return $ do
          logRewrite "Redundant.Align.Project.Right" q
          -- Take the columns from the left and the expressions from
          -- the right projection. Since expressions are applied after
          -- the zip, their column references have to be shifted.
          let e' = appExprSnd $(v "e")
          zipNode <- insert $ BinOp Align $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project e') zipNode |])

zipProjectRight ::VSLRule TExpr TExpr ()
zipProjectRight q =
  $(dagPatMatch 'q "R1 ((q1) Zip (Project e (q2)))"
    [| do
        return $ do
          logRewrite "Redundant.Zip.Project.Right" q
          -- Take the columns from the left and the expressions from
          -- the right projection. Since expressions are applied after
          -- the zip, their column references have to be shifted.
          let e' = appExprSnd $(v "e")
          zipNode <- insert $ BinOp Zip $(v "q1") $(v "q2")
          r1Node  <- insert $ UnOp R1 zipNode
          void $ replaceWithNew q $ UnOp (Project e') r1Node |])

-- fromConst :: Monad m => ConstPayload -> m ScalarVal
-- fromConst (ConstPL val) = return val
-- fromConst NonConstPL    = fail "not a constant"

-- -- | This rewrite is valid because we statically know that both
-- -- vectors have the same length.
-- alignConstLeft ::VSLRule TExpr TExpr BottomUpProps
-- alignConstLeft q =
--   $(dagPatMatch 'q "(q1) Align (q2)"
--     [| do
--         VProp (ConstVec ps) <- constProp <$> properties $(v "q1")
--         w2                  <- vectorWidth . vectorTypeProp <$> properties $(v "q2")
--         vals                <- mapM fromConst ps

--         return $ do
--             logRewrite "Redundant.Align.Constant.Left" q
--             let proj = map Constant vals ++ map Column [1..w2]
--             void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

-- alignConstRight ::VSLRule TExpr TExpr BottomUpProps
-- alignConstRight q =
--   $(dagPatMatch 'q "(q1) Align (q2)"
--     [| do
--         w1                  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
--         VProp (ConstVec ps) <- constProp <$> properties $(v "q2")
--         vals                <- mapM fromConst ps

--         return $ do
--             logRewrite "Redundant.Align.Constant.Right" q
--             let proj = map Column [1..w1] ++ map Constant vals
--             void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

-- -- | In contrast to the 'Align' version ('alignConstLeft') this rewrite is only
-- -- valid if we can statically determine that both input vectors have the same
-- -- length. If the constant vector was shorter, overhanging elements from the
-- -- non-constant vector would need to be discarded. In general, we can only
-- -- determine equal length for the special case of length one.
-- --
-- -- Since we use Zip here, we have to ensure that the constant is in the same
-- -- segment as the entry from the non-constant tuple. At the moment, we can
-- -- guarantee this only for unit-segment vectors.
-- zipConstLeft ::VSLRule TExpr TExpr BottomUpProps
-- zipConstLeft q =
--   $(dagPatMatch 'q "R1 ((q1) Zip (q2))"
--     [| do

--         prop1               <- properties $(v "q1")
--         VProp card1         <- return $ card1Prop prop1
--         VProp (ConstVec ps) <- return $ constProp prop1
--         VProp UnitSegP      <- return $ segProp prop1

--         prop2               <- properties $(v "q2")
--         VProp card2         <- return $ card1Prop prop2
--         w2                  <- vectorWidth . vectorTypeProp <$> properties $(v "q2")
--         VProp UnitSegP      <- return $ segProp prop2

--         vals                <- mapM fromConst ps
--         predicate $ card1 && card2

--         return $ do
--             logRewrite "Redundant.Zip.Constant.Left" q
--             let proj = map Constant vals ++ map Column [1..w2]
--             void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

-- zipConstRight ::VSLRule TExpr TExpr BottomUpProps
-- zipConstRight q =
--   $(dagPatMatch 'q "R1 ((q1) Zip (q2))"
--     [| do
--         prop1               <- properties $(v "q1")
--         VProp card1         <- return $ card1Prop prop1
--         w1                  <- vectorWidth . vectorTypeProp <$> properties $(v "q1")
--         VProp UnitSegP      <- return $ segProp prop1

--         prop2               <- properties $(v "q2")
--         VProp card2         <- return $ card1Prop prop2
--         VProp (ConstVec ps) <- return $ constProp prop2
--         VProp UnitSegP      <- return $ segProp prop2


--         vals                  <- mapM fromConst ps
--         predicate $ card1 && card2

--         return $ do
--             logRewrite "Redundant.Zip.Constant.Right" q
--             let proj = map Column [1..w1] ++ map Constant vals
--             void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

zipZipLeft ::VSLRule TExpr TExpr ()
zipZipLeft q =
  $(dagPatMatch 'q "(q1) Zip (qz=(q11) [Zip | Align] (_))"
     [| do
         predicate $ $(v "q1") == $(v "q11")

         return $ do
             logRewrite "Redundant.Zip/Align.Zip.Left" q
             let e = VMkTuple [ VTupElem First VInput
                              , VInput
                              ]
             void $ replaceWithNew q $ UnOp (Project e) $(v "qz") |])

alignWinRight ::VSLRule TExpr TExpr ()
alignWinRight q =
  $(dagPatMatch 'q "(q1) Align (qw=WinFun _ (q2))"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         return $ do
             logRewrite "Redundant.Align.Self.Win.Right" q
             -- We get all columns from the left input. The WinAggr
             -- operator produces the input column followed by the
             -- window function result.
             let e = VMkTuple [ VTupElem First VInput
                              , VInput
                              ]
             void $ replaceWithNew q $ UnOp (Project e) $(v "qw") |])

zipWinRight ::VSLRule TExpr TExpr ()
zipWinRight q =
  $(dagPatMatch 'q "R1 ((q1) Zip (qw=WinFun _ (q2)))"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         return $ do
             logRewrite "Redundant.Zip.Self.Win.Right" q
             -- We get all columns from the left input. The WinAggr
             -- operator produces the input column followed the window
             -- function result.
             let e = VMkTuple [ VTupElem First VInput
                              , VInput
                              ]
             void $ replaceWithNew q $ UnOp (Project e) $(v "qw") |])

-- | Remove a Zip operator when the right input consists of two window
-- operators.
--
-- FIXME this should be solved properly for the general case.
-- zipWinRight2 ::VSLRule TExpr TExpr BottomUpProps
-- zipWinRight2 q =
--   $(dagPatMatch 'q "R1 ((q1) Zip (qw=WinFun _ (WinFun _ (q2))))"
--      [| do
--          predicate $ $(v "q1") == $(v "q2")

--          w <- vectorWidth . vectorTypeProp <$> properties $(v "q1")

--          return $ do
--              logRewrite "Redundant.Zip.Self.Win.Right.Double" q
--              -- We get all columns from the left input. The WinAggr
--              -- operator produces the input column followed the window
--              -- function result.
--              let proj = map Column $ [1 .. w] ++ [1 .. w] ++ [w+1, w+2]
--              -- logGeneral ("zipWinRight " ++ show proj)
--              void $ replaceWithNew q $ UnOp (Project proj) $(v "qw") |])

alignWinLeft ::VSLRule TExpr TExpr ()
alignWinLeft q =
  $(dagPatMatch 'q "(qw=WinFun _ (q1)) Align (q2)"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         return $ do
             logRewrite "Redundant.Align.Self.Win.Left" q
             -- We get all input columns plus the window function
             -- output from the left. From the right we get all input
             -- columns.
             let e = VMkTuple [ VInput
                              , VTupElem First VInput
                              ]
             void $ replaceWithNew q $ UnOp (Project e) $(v "qw") |])

-- | If the output of a window operator is zipped with its own input, we can
-- remove the Zip operator.
zipWinLeft ::VSLRule TExpr TExpr ()
zipWinLeft q =
  $(dagPatMatch 'q "R1 ((qw=WinFun _ (q1)) Zip (q2))"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         return $ do
             logRewrite "Redundant.Zip.Self.Win.Left" q
             -- We get all input columns plus the window function
             -- output from the left. From the right we get all input
             -- columns.
             let e = VMkTuple [ VInput
                              , VTupElem First VInput
                              ]
             void $ replaceWithNew q $ UnOp (Project e) $(v "qw") |])

isPrecedingFrameSpec :: FrameSpec -> Bool
isPrecedingFrameSpec fs =
    case fs of
        FAllPreceding -> True
        FNPreceding _ -> True

alignWinRightPush ::VSLRule TExpr TExpr ()
alignWinRightPush q =
  $(dagPatMatch 'q "(q1) Align (WinFun args (q2))"
    [| do
        let (winFun, frameSpec) = $(v "args")
        predicate $ isPrecedingFrameSpec frameSpec

        return $ do
            logRewrite "Redundant.Align.Win.Right" q
            zipNode <- insert $ BinOp Align $(v "q1") $(v "q2")
            let winFun' = appExprSnd <$> winFun
                args'   = (winFun', frameSpec)
            void $ replaceWithNew q $ UnOp (WinFun args') zipNode |])

alignGroupJoinRight ::VSLRule TExpr TExpr ()
alignGroupJoinRight q =
  $(dagPatMatch 'q "(qo) Align (gj=(qo1) GroupJoin _ (_))"
    [| do
        predicate $ $(v "qo") == $(v "qo1")
        return $ do
            logRewrite "Redundant.Align.GroupJoin.Right" q
            -- In the result, replicate the columns from the outer
            -- vector to keep the schema intact.
            let e = VMkTuple [ VTupElem First VInput
                             , VInput
                             ]
            void $ replaceWithNew q $ UnOp (Project e) $(v "gj") |])

alignGroupJoinLeft ::VSLRule TExpr TExpr ()
alignGroupJoinLeft q =
  $(dagPatMatch 'q "(gj=(qo1) GroupJoin _ (_)) Align (qo)"
    [| do
        predicate $ $(v "qo") == $(v "qo1")
        return $ do
            logRewrite "Redundant.Align.GroupJoin.Left" q
            -- In the result, replicate the columns from the outer
            -- vector to keep the schema intact.
            let e = VMkTuple [ VInput
                             , VTupElem First VInput
                             ]
            void $ replaceWithNew q $ UnOp (Project e) $(v "gj") |])

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
-- unboxNumber ::VSLRule TExpr TExpr Properties
-- unboxNumber q =
--   $(dagPatMatch 'q "R1 ((Number (qo)) UnboxSng (qi))"
--     [| do
--         VProp (Just reqCols) <- reqColumnsProp . td <$> properties q
--         VProp (VTDataVec wo) <- vectorTypeProp . bu <$> properties $(v "qo")
--         VProp (VTDataVec wi) <- vectorTypeProp . bu <$> properties $(v "qi")
--         predicate $ (wo+1) `notElem` reqCols

--         return $ do
--             logRewrite "Redundant.Unbox.Number" q
--             -- FIXME HACKHACKHACK We have to insert a dummy column in
--             -- place of the number column to avoid destroying column
--             -- indexes.
--             let proj = map Column [1..wo]
--                        ++ [Constant $ IntV 0xdeadbeef]
--                        ++ map Column [wo+1..wi+wo]
--             unboxNode <- insert $ BinOp UnboxSng $(v "qo") $(v "qi")
--             r1Node    <- insert $ UnOp R1 unboxNode
--             void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

-- | If singleton scalar elements in an inner vector (with singleton
-- segments) are unboxed using an outer vector and then aligned with
-- the same outer vector, we can eliminate the align, because the
-- positional alignment is implicitly performed by the UnboxSng
-- operator. We exploit the fact that UnboxSng is only a
-- specialized join which nevertheless produces payload columns from
-- both inputs.
alignUnboxSngRight ::VSLRule TExpr TExpr ()
alignUnboxSngRight q =
  $(dagPatMatch 'q "(q11) Align (qu=R1 ((q12) UnboxSng (_)))"
     [| do
         predicate $ $(v "q11") == $(v "q12")
         return $ do
             logRewrite "Redundant.Align.UnboxSng.Right" q

             -- Keep the original schema intact by duplicating columns
             -- from the left input (UnboxSng produces columns from
             -- its left and right inputs).
             let e = VMkTuple [ VTupElem First VInput
                              , VInput
                              ]

             -- Keep only the unboxing operator, together with a
             -- projection that keeps the original output schema
             -- intact.
             void $ replaceWithNew q $ UnOp (Project e) $(v "qu") |])

-- | See Align.UnboxSng.Right
alignUnboxSngLeft ::VSLRule TExpr TExpr ()
alignUnboxSngLeft q =
  $(dagPatMatch 'q "(qu=R1 ((q11) UnboxSng (_))) Align (q12)"
     [| do
         predicate $ $(v "q11") == $(v "q12")
         return $ do
             logRewrite "Redundant.Align.UnboxSng.Left" q

             -- Keep the original schema intact by duplicating columns
             -- from the left input (UnboxSng produces columns from
             -- its left and right inputs).
             let e = VMkTuple [ VInput
                              , VTupElem First VInput
                              ]

             -- Keep only the unboxing operator, together with a
             -- projection that keeps the original output schema
             -- intact.
             void $ replaceWithNew q $ UnOp (Project e) $(v "qu") |])

-- | If singleton scalar elements in an inner vector (with singleton
-- segments) are unboxed using an outer vector and then aligned with
-- the same outer vector, we can eliminate the align, because the
-- positional alignment is implicitly performed by the UnboxSng
-- operator. We exploit the fact that UnboxSng is only a
-- specialized join which nevertheless produces payload columns from
-- both inputs.
alignUnboxDefaultRight ::VSLRule TExpr TExpr ()
alignUnboxDefaultRight q =
  $(dagPatMatch 'q "(q11) Align (qu=R1 ((q12) UnboxDefault _ (_)))"
     [| do
         predicate $ $(v "q11") == $(v "q12")
         return $ do
             logRewrite "Redundant.Align.UnboxDefault.Right" q

             -- Keep the original schema intact by duplicating columns
             -- from the left input (UnboxSng produces columns from
             -- its left and right inputs).
             let e = VMkTuple [ VTupElem First VInput
                              , VInput
                              ]

             -- Keep only the unboxing operator, together with a
             -- projection that keeps the original output schema
             -- intact.
             void $ replaceWithNew q $ UnOp (Project e) $(v "qu") |])

-- | See Align.UnboxSng.Right
alignUnboxDefaultLeft ::VSLRule TExpr TExpr ()
alignUnboxDefaultLeft q =
  $(dagPatMatch 'q "(qu=R1 ((q11) UnboxDefault _ (_))) Align (q12)"
     [| do
         predicate $ $(v "q11") == $(v "q12")
         return $ do
             logRewrite "Redundant.Align.UnboxDefault.Left" q

             -- Keep the original schema intact by duplicating columns
             -- from the left input (UnboxDefault produces columns from
             -- its left and right inputs).
             let e = VMkTuple [ VInput
                              , VTupElem First VInput
                              ]

             -- Keep only the unboxing operator, together with a
             -- projection that keeps the original output schema
             -- intact.
             void $ replaceWithNew q $ UnOp (Project e) $(v "qu") |])

-- | A CartProduct output is aligned with some other vector. If one of
-- the CartProduct inputs has cardinality one, the other CartProduct
-- input determines the length of the result vector. From the original
-- structure we can derive that 'q11' and the CartProduct result are
-- aligned. Consequentially, 'q11 and 'q12' (the left CartProduct
-- input) must be aligned as well.
alignCartProdRight ::VSLRule TExpr TExpr BottomUpProps
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
-- scalarConditional ::VSLRule TExpr TExpr ()
-- scalarConditional q =
--   $(dagPatMatch 'q "R1 (Combine (Project predProj (q1)) (Project thenProj (R1 (Select pred2 (q2)))) (Project elseProj (R1 (Select negPred (q3)))))"
--     [| do
--         -- All branches must work on the same input vector
--         predicate $ $(v "q1") == $(v "q2") && $(v "q1") == $(v "q3")

--         -- The condition projection as well as the projections for
--         -- then and else branches must produce single columns.
--         [predExpr] <- return $(v "predProj")
--         [thenExpr] <- return $(v "thenProj")
--         [elseExpr] <- return $(v "elseProj")

--         -- The condition for the boolean vector must be the same as
--         -- the selection condition for the then-branch.
--         predicate $ predExpr == $(v "pred2")

--         -- The selection condition must be the negated form of the
--         -- then-condition.
--         predicate $ UnApp (SUBoolOp Not) predExpr == $(v "negPred")

--         return $ do
--           logRewrite "Redundant.ScalarConditional" q
--           void $ replaceWithNew q $ UnOp (Project [If predExpr thenExpr elseExpr]) $(v "q1") |])

------------------------------------------------------------------------------
-- Projection pullup

pullProjectGroupJoinLeft ::VSLRule TExpr TExpr ()
pullProjectGroupJoinLeft q =
  $(dagPatMatch 'q "(Project e (q1)) GroupJoin args (q2)"
    [| do
        let (l1, l2, p, as) = $(v "args")
        return $ do
            logRewrite "Redundant.Project.GroupJoin.Left" q
            let p'  = inlineJoinPredLeft $(v "e") p
                as' = fmap (fmap (mergeExpr $ appExprFst $(v "e"))) as
                e'  = appExprFst $(v "e")

            joinNode <- insert $ BinOp (GroupJoin (l1, l2, p', as')) $(v "q1") $(v "q2")
            void $ replaceWithNew q $ UnOp (Project e') joinNode |])

pullProjectGroupJoinRight ::VSLRule TExpr TExpr ()
pullProjectGroupJoinRight q =
  $(dagPatMatch 'q "(q1) GroupJoin args (Project e (q2))"
    [| do
        let (l1, l2, p, as) = $(v "args")
        return $ do
            logRewrite "Redundant.Project.GroupJoin.Right" q
            let p'        = inlineJoinPredRight e p
                -- Shift column names in the projection expressions to account
                -- for the name shift due to the join.
                as'        = fmap (fmap (mergeExpr $ appExprSnd $(v "e"))) as

            void $ replaceWithNew q $ BinOp (GroupJoin (l1, l2, p', as')) $(v "q1") $(v "q2") |])

pullProjectMaterialize ::VSLRule TExpr TExpr BottomUpProps
pullProjectMaterialize q =
  $(dagPatMatch 'q "R1 ((q1) Materialize (Project p (q2)))"
    [| return $ do
            logRewrite "Redundant.Project.Materialize" q
            repNode <- insert $ BinOp Materialize $(v "q1") $(v "q2")
            r1Node  <- replaceWithNew q $ UnOp R1 repNode
            void $ replaceWithNew q $ UnOp (Project $(v "p")) r1Node

            -- FIXME relink R2 parents
            |])

pullProjectNestJoinLeft ::VSLRule TExpr TExpr ()
pullProjectNestJoinLeft q =
  $(dagPatMatch 'q "R1 ((Project e (q1)) NestJoin args (q2))"
    [| do
        return $ do
            logRewrite "Redundant.Project.NestJoin.Left" q
            let (l1, l2, p) = $(v "args")
                e'          = appExprFst $(v "e")
                p'          = inlineJoinPredLeft $(v "e") p

            joinNode <- insert $ BinOp (NestJoin (l1, l2, p')) $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 joinNode
            void $ replaceWithNew q $ UnOp (Project e') r1Node

            -- FIXME relink R2 and R3 parents
            |])

pullProjectNestJoinRight ::VSLRule TExpr TExpr ()
pullProjectNestJoinRight q =
  $(dagPatMatch 'q "R1 ((q1) NestJoin args (Project e (q2)))"
    [| do
        return $ do
            logRewrite "Redundant.Project.NestJoin.Right" q
            let e' = appExprSnd $(v "e")
                (l1, l2, p) = $(v "args")
                p' = inlineJoinPredRight $(v "e") p

            joinNode <- insert $ BinOp (NestJoin (l1, l2, p')) $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 joinNode
            void $ replaceWithNew q $ UnOp (Project e') r1Node

            -- FIXME relink R2 and R3 parents
            |])

pullProjectCartProductLeft ::VSLRule TExpr TExpr ()
pullProjectCartProductLeft q =
  $(dagPatMatch 'q "R1 ((Project e (q1)) CartProduct (q2))"
    [| do
        return $ do
            logRewrite "Redundant.Project.CartProduct.Left" q
            let e' = appExprFst $(v "e")

            prodNode <- insert $ BinOp CartProduct $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 prodNode
            void $ replaceWithNew q $ UnOp (Project e') r1Node

            -- FIXME relink R2 and R3 parents
            |])

pullProjectCartProductRight ::VSLRule TExpr TExpr ()
pullProjectCartProductRight q =
  $(dagPatMatch 'q "R1 ((q1) CartProduct (Project e (q2)))"
    [| do
        return $ do
            logRewrite "Redundant.Project.CartProduct.Right" q
            let e' = appExprSnd $(v "e")

            prodNode <- insert $ BinOp CartProduct $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 prodNode
            void $ replaceWithNew q $ UnOp (Project e') r1Node

            -- FIXME relink R2 and R3 parents
            |])


pullProjectNumber ::VSLRule TExpr TExpr ()
pullProjectNumber q =
  $(dagPatMatch 'q "Number (Project e (q1))"
    [| do
         return $ do
             logRewrite "Redundant.Project.Number" q

             -- We have to preserve the numbering column in the
             -- pulled-up projection.
             let e' = appExprFst $(v "e")
             numberNode <- insert $ UnOp Number $(v "q1")
             void $ replaceWithNew q $ UnOp (Project e') numberNode |])

pullProjectSort ::VSLRule TExpr TExpr ()
pullProjectSort q =
  $(dagPatMatch 'q "R1 (Sort se (Project e (q1)))"
    [| return $ do
           logRewrite "Redundant.Project.Sort" q
           let se' = partialEval $ mergeExpr $(v "e") $(v "se")
           sortNode <- insert $ UnOp (Sort se') $(v "q1")
           r1Node   <- insert (UnOp R1 sortNode)
           void $ replaceWithNew q $ UnOp (Project $(v "e")) r1Node |])

pullProjectUnboxSngLeft ::VSLRule TExpr TExpr ()
pullProjectUnboxSngLeft q =
  $(dagPatMatch 'q "R1 ((Project e (q1)) UnboxSng (q2))"
    [| do
         return $ do
           logRewrite "Redundant.Project.UnboxSng" q

           -- Employ projection expressions on top of the unboxing
           -- operator, add right input columns.
           let e' = appExprFst $(v "e")
           unboxNode <- insert $ BinOp UnboxSng $(v "q1") $(v "q2")
           r1Node    <- insert $ UnOp R1 unboxNode

           void $ replaceWithNew q $ UnOp (Project e') r1Node |])

pullProjectUnboxDefaultLeft ::VSLRule TExpr TExpr ()
pullProjectUnboxDefaultLeft q =
  $(dagPatMatch 'q "R1 ((Project e (q1)) UnboxDefault d (q2))"
    [| do
         return $ do
           logRewrite "Redundant.Project.UnboxDefault" q

           -- Employ projection expressions on top of the unboxing
           -- operator, add right input columns.
           let e' = appExprFst $(v "e")
           unboxNode <- insert $ BinOp (UnboxDefault $(v "d")) $(v "q1") $(v "q2")
           r1Node    <- insert $ UnOp R1 unboxNode

           void $ replaceWithNew q $ UnOp (Project e') r1Node |])

pullProjectUnboxSngRight ::VSLRule TExpr TExpr ()
pullProjectUnboxSngRight q =
  $(dagPatMatch 'q "R1 ((q1) UnboxSng (Project e (q2)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.UnboxSng" q

           -- Preserve left input columns on top of the unboxing
           -- operator and add right input expressions with shifted
           -- columns.
           let e' = appExprSnd $(v "e")

           unboxNode <- insert $ BinOp UnboxSng $(v "q1") $(v "q2")
           r1Node    <- insert $ UnOp R1 unboxNode

           void $ replaceWithNew q $ UnOp (Project e') r1Node |])

pullProjectReplicateScalarRight ::VSLRule TExpr TExpr ()
pullProjectReplicateScalarRight q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateScalar (Project e (q2)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.ReplicateScalar" q
           let e' = appExprSnd $(v "e")
           distNode <- insert $ BinOp ReplicateScalar $(v "q1") $(v "q2")
           r1Node   <- insert $ UnOp R1 distNode
           void $ replaceWithNew q $ UnOp (Project e') r1Node |])

pullProjectMergeMap ::VSLRule TExpr TExpr ()
pullProjectMergeMap q =
  $(dagPatMatch 'q "MergeMap (Project _ (q1))"
    [| return $ do
           logRewrite "Redundant.Project.MergeMap" q
           void $ replaceWithNew q $ UnOp MergeMap $(v "q1") |])

pullProjectUnitMap ::VSLRule TExpr TExpr ()
pullProjectUnitMap q =
  $(dagPatMatch 'q "UnitMap (Project _ (q1))"
    [| return $ do
           logRewrite "Redundant.Project.UnitMap" q
           void $ replaceWithNew q $ UnOp UnitMap $(v "q1") |])

--------------------------------------------------------------------------------
-- Rewrites that deal with nested structures and propagation vectors.

--------------------------------------------------------------------------------
-- Eliminating operators whose output is not required

-- notReqNumber ::VSLRule TExpr TExpr Properties
-- notReqNumber q =
--   $(dagPatMatch 'q "Number (q1)"
--     [| do
--         w <- vectorWidth . vectorTypeProp . bu <$> properties $(v "q1")
--         VProp (Just reqCols) <- reqColumnsProp . td <$> properties $(v "q")

--         -- The number output in column w + 1 must not be required
--         predicate $ all (<= w) reqCols

--         return $ do
--           logRewrite "Redundant.Req.Number" q
--           -- Add a dummy column instead of the number output to keep
--           -- column references intact.
--           let proj = map Column [1..w] ++ [Constant $ IntV 0xdeadbeef]
--           void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

--------------------------------------------------------------------------------
-- Classical relational algebra rewrites

-- | Merge a selection that refers to both sides of a cartesian
-- product operators' inputs into a join.
selectCartProd ::VSLRule TExpr TExpr ()
selectCartProd q =
  $(dagPatMatch 'q "R1 (Select p (R1 ((q1) CartProduct (q2))))"
    [| do
        VBinApp (SBRelOp op) e1 e2 <- return $(v "p")

        -- The left operand column has to be from the left input, the
        -- right operand from the right input.
        predicate $ idxOnly (== First) e1
        predicate $ idxOnly (== (Next First)) e2

        return $ do
            logRewrite "Redundant.Relational.Join" q
            let e1' = mergeExpr (VMkTuple [VInput, VInput]) e1
            let e2' = mergeExpr (VMkTuple [VInput, VInput]) e2
            let joinPred = singlePred $ JoinConjunct e1' op e2'
            joinNode <- insert $ BinOp (ThetaJoin (Direct, Direct, joinPred)) $(v "q1") $(v "q2")
            void $ replaceWithNew q $ UnOp R1 joinNode |])

--------------------------------------------------------------------------------
-- Normalization rules for segment aggregation

-- | Apply a singleton unbox operator before an align operator. By unboxing
-- early, we hope to be able to eliminate unboxing (e.g. by combining it with an
-- Fold and Group operator).
--
-- Note: We could either push into the left or right align input. For no good
-- reason, we choose the right side. When we deal with a self-align, this will
-- not matter. There might however be plans where the left side would make more
-- sense and we might get stuck.
pushUnboxSngAlign ::VSLRule TExpr TExpr ()
pushUnboxSngAlign q =
  $(dagPatMatch 'q "R1 (((q1) Align (q2)) UnboxSng (q3))"
    [| return $ do
           logRewrite "Redundant.UnboxSng.Push.Align" q
           let e = VMkTuple [ VMkTuple [ VTupElem First VInput
                                       , VTupElem First (VTupElem (Next First) VInput)
                                       ]
                            , VTupElem (Next First) (VTupElem (Next First) VInput)
                            ]
           unboxNode <- insert $ BinOp UnboxSng $(v "q2") $(v "q3")
           r1Node    <- insert $ UnOp R1 unboxNode
           alignNode <- insert $ BinOp Align $(v "q1") r1Node
           void $ replaceWithNew q $ UnOp (Project e) alignNode
     |])

-- | Unbox singletons early, namely before distributing another singleton.
--
-- Note: the same comment as for pushUnboxSngAlign applies.
pushUnboxSngReplicateScalar ::VSLRule TExpr TExpr ()
pushUnboxSngReplicateScalar q =
  $(dagPatMatch 'q "R1 ((R1 ((q1) ReplicateScalar (q2))) UnboxSng (q3))"
    [| return $ do
           logRewrite "Redundant.UnboxSng.Push.ReplicateScalar" q
           let e = VMkTuple [ VMkTuple [ VTupElem First VInput
                                       , VTupElem First (VTupElem (Next First) VInput)
                                       ]
                            , VTupElem (Next First) (VTupElem (Next First) VInput)
                            ]
           unboxNode <- insert $ BinOp UnboxSng $(v "q2") $(v "q3")
           r1Node    <- insert $ UnOp R1 unboxNode
           distNode  <- insert $ BinOp ReplicateScalar $(v "q1") r1Node
           r1Node'   <- insert $ UnOp R1 distNode
           void $ replaceWithNew q $ UnOp (Project e) r1Node'
     |])

--------------------------------------------------------------------------------
-- Pull up number operators

pullNumberReplicateSeg ::VSLRule TExpr TExpr ()
pullNumberReplicateSeg q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateSeg (Number (q2)))"
    [| return $ do
          logRewrite "Redundant.ReplicateSeg.Number" q
          let e = VMkTuple [ VMkTuple [ VTupElem First VInput
                                      , VTupElem First (VTupElem (Next First) VInput)
                                      ]
                           , VTupElem (Next First) (VTupElem (Next First) VInput)
                           ]
          repNode    <- insert $ BinOp ReplicateSeg $(v "q1") $(v "q2")
          r1Node     <- insert $ UnOp R1 repNode
          numberNode <- insert $ UnOp Number r1Node
          void $ replaceWithNew q $ UnOp (Project e) numberNode
     |])

pullNumberAlignLeft ::VSLRule TExpr TExpr ()
pullNumberAlignLeft q =
  $(dagPatMatch 'q "(Number (q1)) Align (q2)"
     [| do
          return $ do
            logRewrite "Redundant.Align.Number.Left" q
            -- Project the number output between left and right columns to
            -- preserve the schema.
            let e = VMkTuple [ VMkTuple [ VTupElem First (VTupElem First VInput)
                                        , VTupElem (Next First) VInput
                                        ]
                             , VTupElem (Next First) (VTupElem First VInput)
                             ]
            alignNode  <- insert $ BinOp Align $(v "q1") $(v "q2")
            numberNode <- insert $ UnOp Number alignNode
            void $ replaceWithNew q $ UnOp (Project e) numberNode
      |]
   )

pullNumberAlignRight ::VSLRule TExpr TExpr ()
pullNumberAlignRight q =
  $(dagPatMatch 'q "(q1) Align (Number (q2))"
     [| do
          return $ do
            logRewrite "Redundant.Align.Number.Right" q
            let e = VMkTuple [ VTupElem First (VTupElem First VInput)
                             , VMkTuple [ VTupElem (Next First) (VTupElem First VInput)
                                        , VTupElem (Next First) VInput
                                        ]
                             ]
            alignNode  <- insert $ BinOp Align $(v "q1") $(v "q2")
            numberNode <- insert $ UnOp Number alignNode
            void $ replaceWithNew q $ UnOp (Project e) numberNode
      |]
   )
