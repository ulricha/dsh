{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VL.Opt.Rewrite.Redundant (removeRedundancy) where

import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Lang

import           Database.DSH.Common.Opt
import           Database.DSH.VL.Opt.Properties.Types
import           Database.DSH.VL.Opt.Properties.VectorType
import           Database.DSH.VL.Opt.Rewrite.Common
import           Database.DSH.VL.Opt.Rewrite.Expressions
import           Database.DSH.VL.Opt.Rewrite.Aggregation
import           Database.DSH.VL.Opt.Rewrite.Window
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
redundantRules = [ pullProjectAppKey
                 , pullProjectAppRep
                 , pullProjectAppFilter
                 , pullProjectAppSort
                 , pullProjectUnboxKey
                 , pullProjectAggrS
                 , pullProjectSort
                 , scalarConditional
                 , pushAggrSSelect
                 , pushAggrSThetaJoinRight
                 , pushUnboxSngSelect
                 , pushAggrSAlign
                 , pushAggrSReplicateScalar
                 , pushUnboxSngAlign
                 , pushUnboxSngReplicateScalar
                 ]


redundantRulesBottomUp :: VLRuleSet BottomUpProps
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
                         , distLiftNestProduct
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
                         , alignWinRightPush
                         , alignUnboxSngRight
                         , alignUnboxSngLeft
                         , alignCartProdRight
                         , alignGroupJoinLeft
                         , alignGroupJoinRight
                         -- , runningAggWinBounded
                         -- , runningAggWinUnbounded
                         , inlineWinAggrProject
                         , pullProjectNumber
                         , constDist
                         , nestJoinChain
                         , pullProjectUnboxSngLeft
                         , pullProjectUnboxSngRight
                         , pullProjectNestJoinLeft
                         , pullProjectNestJoinRight
                         , pullProjectGroupJoinLeft
                         , pullProjectGroupJoinRight
                         , pullProjectReplicateScalarRight
                         , selectCartProd
                         , pushUnboxSngThetaJoinRight
                         ]

redundantRulesAllProps :: VLRuleSet Properties
redundantRulesAllProps = [ unreferencedReplicateNest
                         , notReqNumber
                         , unboxNumber
                         ]

--------------------------------------------------------------------------------
--

unwrapConstVal :: ConstPayload -> VLMatch p ScalarVal
unwrapConstVal (ConstPL val) = return val
unwrapConstVal  NonConstPL   = fail "not a constant"

-- | If the left input of a dist operator is constant, a normal projection
-- can be used because the Dist* operators keeps the shape of the
-- right input.
constDist :: VLRule BottomUpProps
constDist q =
  $(dagPatMatch 'q "R1 ((q1) [ReplicateNest | ReplicateScalar] (q2))"
    [| do
         VProp (ConstVec constCols) <- constProp <$> properties $(v "q1")
         VProp (VTDataVec w)        <- vectorTypeProp <$> properties $(v "q2")
         constVals                  <- mapM unwrapConstVal constCols

         return $ do
              logRewrite "Redundant.Const.ReplicateNest" q
              let proj = map Constant constVals ++ map Column [1..w]
              void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

-- | If a vector is distributed over an inner vector in a segmented
-- way, check if the vector's columns are actually referenced/required
-- downstream. If not, we can remove the ReplicateNest altogether, as the
-- shape of the inner vector is not changed by ReplicateNest.
unreferencedReplicateNest :: VLRule Properties
unreferencedReplicateNest q =
  $(dagPatMatch 'q  "R1 ((q1) ReplicateNest (q2))"
    [| do
        VProp (Just reqCols) <- reqColumnsProp <$> td <$> properties q
        VProp (VTDataVec w1) <- vectorTypeProp <$> bu <$> properties $(v "q1")
        VProp (VTDataVec w2) <- vectorTypeProp <$> bu <$> properties $(v "q2")

        -- Check that only columns from the right input are required
        predicate $ all (> w1) reqCols

        return $ do
          logRewrite "Redundant.Unreferenced.ReplicateNest" q

          -- FIXME HACKHACKHACK
          let padProj = [ Constant $ IntV 0xdeadbeef | _ <- [1..w1] ]
                        ++
                        [ Column i | i <- [1..w2] ]

          void $ replaceWithNew q $ UnOp (Project padProj) $(v "q2") |])

-- | Remove a ReplicateNest if the outer vector is aligned with a
-- NestProduct that uses the same outer vector.
distLiftNestProduct :: VLRule BottomUpProps
distLiftNestProduct q =
  $(dagPatMatch 'q "R1 ((qo) ReplicateNest (R1 ((qo1) NestProduct (qi))))"
    [| do
        predicate $ $(v "qo") == $(v "qo1")

        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "qo")
        w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "qi")

        return $ do
            logRewrite "Redundant.ReplicateNest.NestProduct" q
            -- Preserve the original schema
            let proj = map Column $ [1..w1] ++ [1..w1] ++ [w1+1..w1+w2]
            prodNode <- insert $ BinOp NestProduct $(v "qo") $(v "qi")
            r1Node   <- insert $ UnOp R1 prodNode
            void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

-- | Remove a ReplicateNest if the outer vector is aligned with a
-- NestJoin that uses the same outer vector.
distLiftNestJoin :: VLRule BottomUpProps
distLiftNestJoin q =
  $(dagPatMatch 'q "R1 ((qo) ReplicateNest (R1 ((qo1) NestJoin p (qi))))"
    [| do
        predicate $ $(v "qo") == $(v "qo1")

        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "qo")
        w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "qi")

        return $ do
            logRewrite "Redundant.ReplicateNest.NestJoin" q
            -- Preserve the original schema
            let proj = map Column $ [1..w1] ++ [1..w1] ++ [w1+1..w1+w2]
            prodNode <- insert $ BinOp (NestJoin $(v "p")) $(v "qo") $(v "qi")
            r1Node   <- insert $ UnOp R1 prodNode
            void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

distLiftProjectLeft :: VLRule BottomUpProps
distLiftProjectLeft q =
  $(dagPatMatch 'q "R1 ((Project ps1 (q1)) ReplicateNest (q2))"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q2")

        return $ do
          logRewrite "Redundant.ReplicateNest.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let proj = $(v "ps1") ++ [ Column $ c + w1 | c <- [1 .. w2]]
          distNode <- insert $ BinOp ReplicateNest $(v "q1") $(v "q2")
          r1Node   <- insert $ UnOp R1 distNode
          void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

distLiftProjectRight :: VLRule BottomUpProps
distLiftProjectRight q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateNest (Project p2 (q2)))"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.ReplicateNest.Project.Right" q
          -- Take the columns from the left and the expressions from
          -- the right projection. Since expressions are applied after
          -- the zip, their column references have to be shifted.
          let proj = [Column c | c <- [1..w1]] ++ [ mapExprCols (+ w1) e | e <- $(v "p2") ]
          distNode <- insert $ BinOp ReplicateNest $(v "q1") $(v "q2")
          r1Node   <- insert $ UnOp R1 distNode
          void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

-- If the same outer vector is propagated twice to an inner vector,
-- one ReplicateNest can be removed. Reasoning: ReplicateNest does not change
-- the shape of the inner vector.
distLiftStacked :: VLRule BottomUpProps
distLiftStacked q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateNest (r1=R1 ((q11) ReplicateNest (q2))))"
     [| do
         predicate $ $(v "q1") == $(v "q11")
         w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
         w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q2")

         return $ do
             logRewrite "Redundant.ReplicateNest.Stacked" q
             let proj = map Column $ [1..w1] ++ [1..w1] ++ [w1+1..w1+w2]
             void $ replaceWithNew q $ UnOp (Project proj) $(v "r1") |])

-- | Pull a selection through a ReplicateNest. The reasoning for
-- correctness is simple: It does not matter wether an element of an
-- inner segment is removed before or after ReplicateNest (on relational
-- level, ReplicateNest maps to join which commutes with selection). The
-- "use case" for this rewrite is not well thought-through yet: We
-- want to push down ReplicateNest to eliminate it or merge it with other
-- operators (e.g. ReplicateNest.Stacked). The usual wisdom would suggest
-- to push selections down, though.
distLiftSelect :: VLRule BottomUpProps
distLiftSelect q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateNest (R1 (Select p (q2))))"
     [| do
         w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
         return $ do
             logRewrite "Redundant.ReplicateNest.Select" q
             let p' = shiftExprCols w1 $(v "p")
             distNode <- insert $ BinOp ReplicateNest $(v "q1") $(v "q2")
             distR1   <- insert $ UnOp R1 distNode
             selNode  <- insert $ UnOp (Select p') distR1
             void $ replaceWithNew q $ UnOp R1 selNode |])

-- | When a ReplicateNest result is aligned with the right (inner) ReplicateNest
-- input, we can eliminate the Align. Reasoning: ReplicateNest does not
-- change the shape of the vector, only adds columns from its right
-- input.
alignedDistRight :: VLRule BottomUpProps
alignedDistRight q =
  $(dagPatMatch 'q "(q21) Align (qr1=R1 ((q1) [ReplicateNest | ReplicateScalar] (q22)))"
    [| do
        predicate $ $(v "q21") == $(v "q22")
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q21")

        return $ do
            logRewrite "Redundant.Dist.Align.Right" q
            let proj = map Column $
                       [w1+1..w1+w2]
                       ++
                       [1..w1]
                       ++
                       [w1+1..w1+w2]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "qr1") |])

-- | When a ReplicateNest result is aligned with the right (inner) ReplicateNest
-- input, we can eliminate the Align. Reasoning: ReplicateNest does not
-- change the shape of the vector, only adds columns from its right
-- input.
alignedDistLeft :: VLRule BottomUpProps
alignedDistLeft q =
  $(dagPatMatch 'q "(qr1=R1 ((q1) [ReplicateNest | ReplicateScalar] (q21))) Align (q22)"
    [| do
        predicate $ $(v "q21") == $(v "q22")
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q21")

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
sameInputAlign :: VLRule BottomUpProps
sameInputAlign q =
  $(dagPatMatch 'q "(q1) Align (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Align.Self" q
          let ps = map Column [1 .. w]
          void $ replaceWithNew q $ UnOp (Project (ps ++ ps)) $(v "q1") |])

-- | Replace an Align operator with a projection if both inputs are the
-- same.
sameInputZip :: VLRule BottomUpProps
sameInputZip q =
  $(dagPatMatch 'q "R1 ((q1) Zip (q2))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Zip.Self" q
          let ps = map Column [1 .. w]
          void $ replaceWithNew q $ UnOp (Project (ps ++ ps)) $(v "q1") |])

-- sameInputZipProject :: VLRule BottomUpProps
-- sameInputZipProject q =
--   $(dagPatMatch 'q "(Project ps1 (q1)) [Zip | Align] (Project ps2 (q2))"
--     [| do
--         predicate $ $(v "q1") == $(v "q2")

--         return $ do
--           logRewrite "Redundant.Zip/Align.Self.Project" q
--           void $ replaceWithNew q $ UnOp (Project ($(v "ps1") ++ $(v "ps2"))) $(v "q1") |])

-- sameInputZipProjectLeft :: VLRule BottomUpProps
-- sameInputZipProjectLeft q =
--   $(dagPatMatch 'q "(Project ps1 (q1)) [Zip | Align] (q2)"
--     [| do
--         predicate $ $(v "q1") == $(v "q2")
--         w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

--         return $ do
--           logRewrite "Redundant.Zip/Align.Self.Project.Left" q
--           let proj = $(v "ps1") ++ (map Column [1..w1])
--           void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

-- sameInputZipProjectRight :: VLRule BottomUpProps
-- sameInputZipProjectRight q =
--   $(dagPatMatch 'q "(q1) [Zip | Align] (Project ps2 (q2))"
--     [| do
--         predicate $ $(v "q1") == $(v "q2")
--         w <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

--         return $ do
--           logRewrite "Redundant.Zip/Align.Self.Project.Right" q
--           let proj = (map Column [1 .. w]) ++ $(v "ps2")
--           void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

alignProjectLeft :: VLRule BottomUpProps
alignProjectLeft q =
  $(dagPatMatch 'q "(Project ps1 (q1)) Align (q2)"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q2")

        return $ do
          logRewrite "Redundant.Align.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let proj = $(v "ps1") ++ [ Column $ c + w1 | c <- [1 .. w2]]
          alignNode <- insert $ BinOp Align $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project proj) alignNode |])

zipProjectLeft :: VLRule BottomUpProps
zipProjectLeft q =
  $(dagPatMatch 'q "R1 ((Project ps1 (q1)) Zip (q2))"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")
        w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q2")

        return $ do
          logRewrite "Redundant.Zip.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let proj = $(v "ps1") ++ [ Column $ c + w1 | c <- [1 .. w2]]
          zipNode <- insert $ BinOp Zip $(v "q1") $(v "q2")
          r1Node  <- insert $ UnOp R1 zipNode
          void $ replaceWithNew q $ UnOp (Project proj) r1Node |])

alignProjectRight :: VLRule BottomUpProps
alignProjectRight q =
  $(dagPatMatch 'q "(q1) Align (Project p2 (q2))"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

        return $ do
          logRewrite "Redundant.Align.Project.Right" q
          -- Take the columns from the left and the expressions from
          -- the right projection. Since expressions are applied after
          -- the zip, their column references have to be shifted.
          let proj = [Column c | c <- [1..w1]] ++ [ mapExprCols (+ w1) e | e <- $(v "p2") ]
          zipNode <- insert $ BinOp Align $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project proj) zipNode |])

zipProjectRight :: VLRule BottomUpProps
zipProjectRight q =
  $(dagPatMatch 'q "R1 ((q1) Zip (Project p2 (q2)))"
    [| do
        w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "q1")

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
alignConstLeft :: VLRule BottomUpProps
alignConstLeft q =
  $(dagPatMatch 'q "(q1) Align (q2)"
    [| do
        VProp (ConstVec ps) <- constProp <$> properties $(v "q1")
        w2                  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")
        vals                <- mapM fromConst ps

        return $ do
            logRewrite "Redundant.Align.Constant.Left" q
            let proj = map Constant vals ++ map Column [1..w2]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

alignConstRight :: VLRule BottomUpProps
alignConstRight q =
  $(dagPatMatch 'q "(q1) Align (q2)"
    [| do
        w1                  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
        VProp (ConstVec ps) <- constProp <$> properties $(v "q2")
        vals                <- mapM fromConst ps

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
  $(dagPatMatch 'q "R1 ((q1) Zip (q2))"
    [| do
        prop1               <- properties $(v "q1")
        VProp card1         <- return $ card1Prop prop1
        VProp (ConstVec ps) <- return $ constProp prop1

        prop2               <- properties $(v "q2")
        VProp card2         <- return $ card1Prop prop2
        w2                  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")

        vals                <- mapM fromConst ps
        predicate $ card1 && card2

        return $ do
            logRewrite "Redundant.Zip.Constant.Left" q
            let proj = map Constant vals ++ map Column [1..w2]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

zipConstRight :: VLRule BottomUpProps
zipConstRight q =
  $(dagPatMatch 'q "R1 ((q1) Zip (q2))"
    [| do
        prop1               <- properties $(v "q1")
        VProp card1         <- return $ card1Prop prop1
        w1                  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

        prop2               <- properties $(v "q2")
        VProp card2         <- return $ card1Prop prop2
        VProp (ConstVec ps) <- return $ constProp prop2


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

alignWinRight :: VLRule BottomUpProps
alignWinRight q =
  $(dagPatMatch 'q "(q1) Align (qw=WinFun _ (q2))"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         w <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

         return $ do
             logRewrite "Redundant.Align.Self.Win.Right" q
             -- We get all columns from the left input. The WinAggr
             -- operator produces the input column followed by the
             -- window function result.
             let proj = map Column $ [1 .. w] ++ [1 .. w] ++ [w+1]
             -- logGeneral ("zipWinRight " ++ show proj)
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qw") |])

zipWinRight :: VLRule BottomUpProps
zipWinRight q =
  $(dagPatMatch 'q "R1 ((q1) Zip (qw=WinFun _ (q2)))"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         w <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

         return $ do
             logRewrite "Redundant.Zip.Self.Win.Right" q
             -- We get all columns from the left input. The WinAggr
             -- operator produces the input column followed the window
             -- function result.
             let proj = map Column $ [1 .. w] ++ [1 .. w] ++ [w+1]
             -- logGeneral ("zipWinRight " ++ show proj)
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qw") |])

alignWinLeft :: VLRule BottomUpProps
alignWinLeft q =
  $(dagPatMatch 'q "(qw=WinFun _ (q1)) Align (q2)"
     [| do
         predicate $ $(v "q1") == $(v "q2")

         w <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

         return $ do
             logRewrite "Redundant.Align.Self.Win.Left" q
             -- We get all input columns plus the window function
             -- output from the left. From the right we get all input
             -- columns.
             let proj = map Column $ [1 .. w] ++ [w+1] ++ [1 .. w]
             void $ replaceWithNew q $ UnOp (Project proj) $(v "qw") |])

zipWinLeft :: VLRule BottomUpProps
zipWinLeft q =
  $(dagPatMatch 'q "R1 ((qw=WinFun _ (q1)) Zip (q2))"
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

alignWinRightPush :: VLRule BottomUpProps
alignWinRightPush q =
  $(dagPatMatch 'q "(q1) Align (WinFun args (q2))"
    [| do
        let (winFun, frameSpec) = $(v "args")
        predicate $ isPrecedingFrameSpec frameSpec
        w1 <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

        return $ do
            logRewrite "Redundant.Align.Win.Right" q
            zipNode <- insert $ BinOp Align $(v "q1") $(v "q2")
            let winFun' = mapWinFun (mapExprCols (\c -> c + w1)) winFun
                args'   = (winFun', frameSpec)
            void $ replaceWithNew q $ UnOp (WinFun args') zipNode |])

alignGroupJoinRight :: VLRule BottomUpProps
alignGroupJoinRight q =
  $(dagPatMatch 'q "(qo) Align (gj=(qo1) GroupJoin _ (_))"
    [| do
        predicate $ $(v "qo") == $(v "qo1")
        w <- vectorWidth <$> vectorTypeProp <$> properties $(v "qo")

        return $ do
            logRewrite "Redundant.Align.GroupJoin.Right" q
            -- In the result, replicate the columns from the outer
            -- vector to keep the schema intact.
            let proj = map Column $ [1..w] ++ [1..w+1]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "gj") |])

alignGroupJoinLeft :: VLRule BottomUpProps
alignGroupJoinLeft q =
  $(dagPatMatch 'q "(gj=(qo1) GroupJoin _ (_)) Align (qo)"
    [| do
        predicate $ $(v "qo") == $(v "qo1")
        w <- vectorWidth <$> vectorTypeProp <$> properties $(v "qo")

        return $ do
            logRewrite "Redundant.Align.GroupJoin.Left" q
            -- In the result, replicate the columns from the outer
            -- vector to keep the schema intact.
            let proj = map Column $ [1..w+1] ++ [1..w]
            void $ replaceWithNew q $ UnOp (Project proj) $(v "gj") |])

-- | If the right (outer) input of Unbox is a NumberS operator and the
-- number output is not required, eliminate it from the outer
-- input. This is correct because NumberS does not change the vertical
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
unboxNumber :: VLRule Properties
unboxNumber q =
  $(dagPatMatch 'q "R1 ((NumberS (qo)) UnboxSng (qi))"
    [| do
        VProp (Just reqCols) <- reqColumnsProp <$> td <$> properties q
        VProp (VTDataVec wo) <- vectorTypeProp <$> bu <$> properties $(v "qo")
        VProp (VTDataVec wi) <- vectorTypeProp <$> bu <$> properties $(v "qi")
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
alignUnboxSngRight :: VLRule BottomUpProps
alignUnboxSngRight q =
  $(dagPatMatch 'q "(q11) Align (qu=R1 ((q12) UnboxSng (q2)))"
     [| do
         predicate $ $(v "q11") == $(v "q12")

         leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q11")
         rightWidth <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")

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
alignUnboxSngLeft :: VLRule BottomUpProps
alignUnboxSngLeft q =
  $(dagPatMatch 'q "(qu=R1 ((q11) UnboxSng (q2))) Align (q12)"
     [| do
         predicate $ $(v "q11") == $(v "q12")

         leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q11")
         rightWidth <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")

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

pullProjectGroupJoinLeft :: VLRule BottomUpProps
pullProjectGroupJoinLeft q =
  $(dagPatMatch 'q "(Project proj (q1)) GroupJoin args (q2)"
    [| do
        let (p, a) = $(v "args")
        leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
        rightWidth <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")

        return $ do
            logRewrite "Redundant.Project.GroupJoin.Left" q
            let proj'     = $(v "proj") ++ [Column $ leftWidth + 1]
                p'        = inlineJoinPredLeft (zip [1..] $(v "proj")) p
                rightCols = [leftWidth+1 .. leftWidth + rightWidth]
                env       = zip [1..] ($(v "proj") ++ map Column rightCols)
                a'        = mapAggrFun (mergeExpr env) a

            joinNode <- insert $ BinOp (GroupJoin (p', a')) $(v "q1") $(v "q2")
            void $ replaceWithNew q $ UnOp (Project proj') joinNode |])

pullProjectGroupJoinRight :: VLRule BottomUpProps
pullProjectGroupJoinRight q =
  $(dagPatMatch 'q "(q1) GroupJoin args (Project proj (q2))"
    [| do
        let (p, a) = $(v "args")
        leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

        return $ do
            logRewrite "Redundant.Project.GroupJoin.Right" q
            let p'        = inlineJoinPredRight (zip [1..] $(v "proj")) p
                leftCols  = [1..leftWidth]
                -- Shift column names in the projection expressions to account
                -- for the name shift due to the join.
                proj'     = map (shiftExprCols leftWidth) $(v "proj")
                env       = zip [1..] (map Column leftCols ++ proj')
                a'        = mapAggrFun (mergeExpr env) a

            void $ replaceWithNew q $ BinOp (GroupJoin (p', a')) $(v "q1") $(v "q2") |])

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
  $(dagPatMatch 'q "NumberS (Project proj (q1))"
    [| do
         w <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

         return $ do
             logRewrite "Redundant.Project.Number" q

             -- We have to preserve the numbering column in the
             -- pulled-up projection.
             let proj' = $(v "proj") ++ [Column $ w + 1]
             numberNode <- insert $ UnOp NumberS $(v "q1")
             void $ replaceWithNew q $ UnOp (Project proj') numberNode |])

pullProjectSort :: VLRule ()
pullProjectSort q =
  $(dagPatMatch 'q "R1 (SortS ses (Project ps (q)))"
    [| do
          return $ do
              logRewrite "Redundant.Project.Sort" q
              let env = zip [1..] $(v "ps")
              let ses' = map (mergeExpr env) $(v "ses")
              sortNode <- insert $ UnOp (SortS ses') $(v "q")
              r1Node   <- insert (UnOp R1 sortNode)
              void $ replaceWithNew q $ UnOp (Project $(v "ps")) r1Node |])

-- Motivation: In order to eliminate or pull up sorting operations in
-- VL rewrites or subsequent stages, payload columns which might
-- induce sort order should be available as long as possible. We
-- assume that the cost of having unrequired columns around is
-- negligible (best case: column store).

pullProjectAppKey :: VLRule ()
pullProjectAppKey q =
  $(dagPatMatch 'q "R1 ((qp) AppKey (Project proj (qv)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.AppKey" q
           rekeyNode <- insert $ BinOp AppKey $(v "qp") $(v "qv")
           r1Node    <- insert $ UnOp R1 rekeyNode
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node |])

pullProjectUnboxSngLeft :: VLRule BottomUpProps
pullProjectUnboxSngLeft q =
  $(dagPatMatch 'q "R1 ((Project proj (q1)) UnboxSng (q2))"
    [| do
         leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")
         rightWidth <- vectorWidth <$> vectorTypeProp <$> properties $(v "q2")

         return $ do
           logRewrite "Redundant.Project.UnboxSng" q

           -- Employ projection expressions on top of the unboxing
           -- operator, add right input columns.
           let proj' = $(v "proj") ++ map Column [ leftWidth + 1 .. leftWidth + rightWidth ]
           unboxNode <- insert $ BinOp UnboxSng $(v "q1") $(v "q2")
           r1Node    <- insert $ UnOp R1 unboxNode

           void $ replaceWithNew q $ UnOp (Project proj') r1Node |])

pullProjectUnboxSngRight :: VLRule BottomUpProps
pullProjectUnboxSngRight q =
  $(dagPatMatch 'q "R1 ((q1) UnboxSng (Project proj (q2)))"
    [| do
         leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

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

pullProjectReplicateScalarRight :: VLRule BottomUpProps
pullProjectReplicateScalarRight q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateScalar (Project p (q2)))"
    [| do
         leftWidth  <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

         return $ do
           logRewrite "Redundant.Project.ReplicateScalar" q
           let p' = map Column [1..leftWidth]
                    ++
                    [ mapExprCols (+ leftWidth) e | e <- $(v "p") ]
           distNode <- insert $ BinOp ReplicateScalar $(v "q1") $(v "q2")
           r1Node   <- insert $ UnOp R1 distNode
           void $ replaceWithNew q $ UnOp (Project p') r1Node |])

pullProjectAppRep :: VLRule ()
pullProjectAppRep q =
  $(dagPatMatch 'q "R1 ((qp) AppRep (Project proj (qv)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.AppRep" q
           repNode <- insert $ BinOp AppRep $(v "qp") $(v "qv")
           r1Node  <- insert $ UnOp R1 repNode
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node |])

pullProjectAppFilter :: VLRule ()
pullProjectAppFilter q =
  $(dagPatMatch 'q "R1 ((q1) AppFilter (Project proj (q2)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.AppFilter" q
           filterNode <- insert $ BinOp AppFilter $(v "q1") $(v "q2")
           r1Node     <- insert $ UnOp R1 filterNode
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node |])

pullProjectAppSort :: VLRule ()
pullProjectAppSort q =
  $(dagPatMatch 'q "R1 ((q1) AppSort (Project proj (q2)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.AppSort" q
           sortNode <- insert $ BinOp AppSort $(v "q1") $(v "q2")
           r1Node   <- insert $ UnOp R1 sortNode
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node |])

pullProjectUnboxKey :: VLRule ()
pullProjectUnboxKey q =
  $(dagPatMatch 'q "UnboxKey (Project _ (q1))"
    [| do
         return $ do
           logRewrite "Redundant.Project.UnboxKey" q
           void $ replaceWithNew q $ UnOp UnboxKey $(v "q1") |])

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
-- Rewrites that deal with nested structures and propagation vectors.

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
  $(dagPatMatch 'q "R1 ((R3 (lj=(xs) NestJoin _ (ys))) AppRep (R1 ((ys1) NestJoin p (zs))))"
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
  $(dagPatMatch 'q "NumberS (q1)"
    [| do
        w <- vectorWidth <$> vectorTypeProp <$> bu <$> properties $(v "q1")
        VProp (Just reqCols) <- reqColumnsProp <$> td <$> properties $(v "q")

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

--------------------------------------------------------------------------------
-- Early aggregation of segments. We try to aggregate segments as early as
-- possible by pushing down segment aggregation operators through segment
-- propagation operators. Aggregating early means that the cardinality of inner
-- vectors is reduced. Ideally, we will be able to merge the AggrS operator with
-- nesting operators (Group, NestJoin) and thereby avoid the materialization of
-- inner segments altogether.
--
-- Amongst others, these rewrites are important to deal with HAVING-like
-- patterns.

-- | If segments are aggregated after they have been filtered due to an outer
-- selection, we can aggregate early before filtering the segments.
pushAggrSSelect :: VLRule ()
pushAggrSSelect q =
  $(dagPatMatch 'q "(R1 (qs1=Select _ (qo))) AggrS af (R1 ((q2=R2 (qs2=Select _ (_))) AppFilter (qi)))"
    [| do
        predicate $ $(v "qs1") == $(v "qs2")

        return $ do
            logRewrite "Redundant.AggrS.Push.Select" q
            aggNode <- insert $ BinOp (AggrS $(v "af")) $(v "qo") $(v "qi")
            appNode <- insert $ BinOp AppFilter $(v "q2") aggNode
            void $ replaceWithNew q $ UnOp R1 appNode |])

-- | Aggregate segments from a right join input before they are replicated as a
-- consequence of a ThetaJoin operator.
pushAggrSThetaJoinRight :: VLRule ()
pushAggrSThetaJoinRight q =
    $(dagPatMatch 'q "(R1 (qj1)) AggrS args (R1 ((qr3=R3 (qj2=(_) ThetaJoin _ (qo2))) AppRep (qi)))"
      [| do
          predicate $ $(v "qj1") == $(v "qj2")
          return $ do
              logRewrite "Redundant.AggrS.Push.ThetaJoin.Right" q
              aggNode <- insert $ BinOp (AggrS $(v "args")) $(v "qo2") $(v "qi")
              repNode <- insert $ BinOp AppRep $(v "qr3") aggNode
              void $ replaceWithNew q $ UnOp R1 repNode
      |])

-- | Unbox singleton segments before they are filtered because of a selection.
-- This rewrite is valid because we only add columns at the end: column
-- references in the selection predicate remain valid.
pushUnboxSngSelect :: VLRule ()
pushUnboxSngSelect q =
  $(dagPatMatch 'q "R1 ((R1 (qs1=Select p (qo))) UnboxSng (R1 ((q2=R2 (qs2=Select _ (_))) AppFilter (qi))))"
    [| do
        predicate $ $(v "qs1") == $(v "qs2")
        return $ do
            logRewrite "Redundant.UnboxSng.Push.Select" q
            unboxNode  <- insert $ BinOp UnboxSng $(v "qo") $(v "qi")
            r1Node     <- insert $ UnOp R1 unboxNode
            selectNode <- insert $ UnOp (Select $(v "p")) r1Node
            void $ replaceWithNew q $ UnOp R1 selectNode |])

-- | Unbox singleton segments before a join (right input). This is an
-- improvement because the replication join is no longer necessary.
pushUnboxSngThetaJoinRight :: VLRule BottomUpProps
pushUnboxSngThetaJoinRight q =
    $(dagPatMatch 'q "R1 (qu=(qr1=R1 (qj1=(qo1) ThetaJoin p (qo2))) UnboxSng (R1 ((R3 (qj2)) AppRep (qi))))"
      [| do
          predicate $ $(v "qj1") == $(v "qj2")
          w1 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "qo1")
          w2 <- liftM (vectorWidth . vectorTypeProp) $ properties $(v "qo2")

          return $ do
              logRewrite "Redundant.UnboxSng.Push.ThetaJoin.Right" q
              -- Insert unboxing in the right input of the join.
              unboxNode   <- insert $ BinOp UnboxSng $(v "qo2") $(v "qi")
              r1UnboxNode <- insert $ UnOp R1 unboxNode
              joinNode    <- insert $ BinOp (ThetaJoin $(v "p")) $(v "qo1") r1UnboxNode
              r1JoinNode  <- insert $ UnOp R1 joinNode
              replace q r1JoinNode

              -- Take care not to duplicate the join operator. We rewire all
              -- original parents to the new join operator and use a projection
              -- to keep the original schema.
              joinParents <- filter (/= $(v "qu")) <$> parents $(v "qr1")
              let proj = map Column [1..w1+w2]
              projNode <- insert $ UnOp (Project proj) r1JoinNode
              forM_ joinParents $ \p -> replaceChild p $(v "qr1") projNode
      |])

--------------------------------------------------------------------------------
-- Normalization rules for segment aggregation

pushAggrSAlign :: VLRule ()
pushAggrSAlign q =
  $(dagPatMatch 'q "((_) Align (q1)) AggrS af (q2)"
    [| do
        return $ do
            logRewrite "Redundant.AggrS.Push.Align" q
            void $ replaceWithNew q $ BinOp (AggrS $(v "af")) $(v "q1") $(v "q2") |])

pushAggrSReplicateScalar :: VLRule ()
pushAggrSReplicateScalar q =
  $(dagPatMatch 'q "(R1 ((_) ReplicateScalar (q1))) AggrS af (q2)"
    [| do
        return $ do
            logRewrite "Redundant.AggrS.Push.ReplicateScalar" q
            void $ replaceWithNew q $ BinOp (AggrS $(v "af")) $(v "q1") $(v "q2") |])

-- | Apply a singleton unbox operator before an align operator. By unboxing
-- early, we hope to be able to eliminate unboxing (e.g. by combining it with an
-- AggrS and Group operator).
--
-- Note: We could either push into the left or right align input. For no good
-- reason, we choose the right side. When we deal with a self-align, this will
-- not matter. There might however be plans where the left side would make more
-- sense and we might get stuck.
pushUnboxSngAlign :: VLRule ()
pushUnboxSngAlign q =
  $(dagPatMatch 'q "R1 (((q1) Align (q2)) UnboxSng (q3))"
    [| do
        return $ do
            logRewrite "Redundant.UnboxSng.Push.Align" q
            unboxNode <- insert $ BinOp UnboxSng $(v "q2") $(v "q3")
            r1Node    <- insert $ UnOp R1 unboxNode
            void $ replaceWithNew q $ BinOp Align $(v "q1") r1Node |])

-- | Unbox singletons early, namely before distributing another singleton.
--
-- Note: the same comment as for pushUnboxSngAlign applies.
pushUnboxSngReplicateScalar :: VLRule ()
pushUnboxSngReplicateScalar q =
  $(dagPatMatch 'q "R1 ((R1 ((q1) ReplicateScalar (q2))) UnboxSng (q3))"
    [| do
        return $ do
            logRewrite "Redundant.UnboxSng.Push.ReplicateScalar" q
            unboxNode <- insert $ BinOp UnboxSng $(v "q2") $(v "q3")
            r1Node    <- insert $ UnOp R1 unboxNode
            distNode  <- insert $ BinOp ReplicateScalar $(v "q1") r1Node
            void $ replaceWithNew q $ UnOp R1 distNode |])
