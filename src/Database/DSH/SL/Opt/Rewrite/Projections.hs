{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TemplateHaskell  #-}

module Database.DSH.SL.Opt.Rewrite.Projections where

-- This module contains rewrites which aim to simplify and merge complex expressions
-- which are expressed through multiple operators.

import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Opt
import           Database.DSH.Common.VectorLang
import           Database.DSH.SL.Lang
import           Database.DSH.SL.Opt.Rewrite.Common

optExpressions :: SLRewrite TExpr TExpr Bool
optExpressions = iteratively $ applyToAll noProps expressionRules

expressionRules :: SLRuleSet TExpr TExpr ()
expressionRules = [ mergeProject
                  , identityProject
                  , pullProjectSelect
                  , pullProjectAppKey
                  , pullProjectAppMap
                  , pullProjectSort
                  , pullProjectMergeSegLeft
                  , pullProjectMergeSegRight
                  , pullProjectNumber
                  , pullProjectSegment
                  , pullProjectUnsegment
                  , pullProjectGroupR1
                  , pullProjectGroupR2
                  , pullProjectGroupAggr
                  , pullProjectUnboxDefaultLeft
                  , pullProjectUnboxSngLeft
                  , pullProjectUnboxSngRight
                  , pullProjectNestJoinLeft
                  , pullProjectNestJoinRight
                  , pullProjectThetaJoinLeft
                  , pullProjectThetaJoinRight
                  , pullProjectFilterJoinLeft
                  , pullProjectFilterJoinRight
                  , pullProjectReplicateVecLeft
                  , pullProjectReplicateVecRight
                  , pullProjectCartProductLeft
                  , pullProjectCartProductRight
                  , pullProjectGroupJoinLeft
                  , pullProjectGroupJoinRight
                  , pullProjectReplicateScalarRight
                  , pullProjectAlignLeft
                  , pullProjectAlignRight
                  , pullProjectDistLiftLeft
                  , pullProjectDistLiftRight
                  ]

mergeProject :: SLRule TExpr TExpr ()
mergeProject q =
  $(dagPatMatch 'q "Project e2 (Project e1 (q1))"
    [| do

        return $ do
          logRewrite "Expr.Merge.11" q
          let e2' = partialEval $ mergeExpr $(v "e1") $(v "e2")
          void $ replaceWithNew q $ UnOp (Project e2') $(v "q1") |])

pullProjectSelect :: SLRule TExpr TExpr ()
pullProjectSelect q =
  $(dagPatMatch 'q "R1 (qs=Select p (Project e (q1)))"
     [| do
        return $ do
          logRewrite "Expr.Merge.Select" q
          let p'  = partialEval $ mergeExpr $(v "e") $(v "p")
          selectNode <- insert $ UnOp (Select p') $(v "q1")
          r1Node     <- insert $ UnOp R1 selectNode
          void $ replaceWithNew q $ UnOp (Project $(v "e")) r1Node

          r2Parents <- lookupR2Parents $(v "qs")

          -- If there are any R2 nodes linking to the original
          -- Restrict operator (i.e. there are inner vectors to which
          -- changes must be propagated), they have to be rewired to
          -- the new Select operator.
          when (not $ null r2Parents) $ do
            qr2' <- insert $ UnOp R2 selectNode
            mapM_ (\qr2 -> replace qr2 qr2') r2Parents |])

identityProject :: SLRule TExpr TExpr ()
identityProject q =
  $(dagPatMatch 'q "Project e (q1)"
    [| do
        TInput <- return $(v "e")

        return $ do
          logRewrite "Project.Identity" q
          replace q $(v "q1") |])

pullProjectDistLiftLeft :: SLRule TExpr TExpr ()
pullProjectDistLiftLeft q =
  $(dagPatMatch 'q "R1 ((Project e (q1)) ReplicateNest (q2))"
    [| do
        return $ do
          logRewrite "Redundant.ReplicateNest.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let e' = appExprFst $(v "e")
          distNode <- insert $ BinOp ReplicateNest $(v "q1") $(v "q2")
          r1Node   <- insert $ UnOp R1 distNode
          void $ replaceWithNew q $ UnOp (Project e') r1Node |])

pullProjectDistLiftRight :: SLRule TExpr TExpr ()
pullProjectDistLiftRight q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateNest (Project e (q2)))"
    [| do
        return $ do
          logRewrite "Redundant.ReplicateNest.Project.Right" q
          let e' = appExprSnd $(v "e")
          distNode <- insert $ BinOp ReplicateNest $(v "q1") $(v "q2")
          r1Node   <- insert $ UnOp R1 distNode
          void $ replaceWithNew q $ UnOp (Project e') r1Node |])

pullProjectAlignLeft :: SLRule TExpr TExpr ()
pullProjectAlignLeft q =
  $(dagPatMatch 'q "(Project e (q1)) Align (q2)"
    [| do
        return $ do
          logRewrite "Redundant.Align.Project.Left" q
          -- Take the projection expressions from the left and the
          -- shifted columns from the right.
          let e' = appExprFst $(v "e")
          alignNode <- insert $ BinOp Align $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project e') alignNode |])

pullProjectAlignRight :: SLRule TExpr TExpr ()
pullProjectAlignRight q =
  $(dagPatMatch 'q "(q1) Align (Project e (q2))"
    [| do
        return $ do
          logRewrite "Redundant.Align.Project.Right" q
          -- Take the projection expressions from the right and the
          -- shifted columns from the left.
          let e' = appExprSnd $(v "e")
          alignNode <- insert $ BinOp Align $(v "q1") $(v "q2")
          void $ replaceWithNew q $ UnOp (Project e') alignNode |])

pullProjectGroupJoinLeft :: SLRule TExpr TExpr ()
pullProjectGroupJoinLeft q =
  $(dagPatMatch 'q "(Project e (q1)) GroupJoin args (q2)"
    [| do
        let (p, as) = $(v "args")
        return $ do
            logRewrite "Redundant.Project.GroupJoin.Left" q
            let p'  = partialEval <$> inlineJoinPredLeft $(v "e") p
                as' = fmap (fmap (partialEval . (mergeExpr $ appExprFst $(v "e")))) as
                e'  = appExprFst $(v "e")

            joinNode <- insert $ BinOp (GroupJoin (p', as')) $(v "q1") $(v "q2")
            void $ replaceWithNew q $ UnOp (Project e') joinNode |])

pullProjectGroupJoinRight :: SLRule TExpr TExpr ()
pullProjectGroupJoinRight q =
  $(dagPatMatch 'q "(q1) GroupJoin args (Project e (q2))"
    [| do
        let (p, as) = $(v "args")
        return $ do
            logRewrite "Redundant.Project.GroupJoin.Right" q
            let p'  = partialEval <$> inlineJoinPredRight e p
                as' = fmap (fmap (partialEval . (mergeExpr $ appExprSnd $(v "e")))) as

            void $ replaceWithNew q $ BinOp (GroupJoin (p', as')) $(v "q1") $(v "q2") |])

pullProjectReplicateVecLeft :: SLRule TExpr TExpr ()
pullProjectReplicateVecLeft q =
  $(dagPatMatch 'q "R1 ((Project proj (q1)) ReplicateVector (q2))"
    [| return $ do
            logRewrite "Redundant.Project.ReplicateVector.Left" q
            repNode <- insert $ BinOp ReplicateVector $(v "q1") $(v "q2")
            r1Node  <- insert $ UnOp R1 repNode
            void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node

            -- FIXME relink R2 parents
            |])

pullProjectReplicateVecRight :: SLRule TExpr TExpr ()
pullProjectReplicateVecRight q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateVector (Project _ (q2)))"
    [| return $ do
            logRewrite "Redundant.Project.ReplicateVector.Right" q
            repNode <- insert $ BinOp ReplicateVector $(v "q1") $(v "q2")
            void $ replaceWithNew q $ UnOp R1 repNode

            -- FIXME relink R2 parents
            |])

pullProjectFilterJoinLeft :: SLRule TExpr TExpr ()
pullProjectFilterJoinLeft q =
  $(dagPatMatch 'q "R1 ((Project e (q1)) [SemiJoin | AntiJoin]@joinOp p (q2))"
    [| do
        return $ do
            logRewrite "Redundant.Project.FilterJoin.Left" q
            let p' = partialEval <$> inlineJoinPredLeft $(v "e") $(v "p")

            joinNode <- insert $ BinOp ($(v "joinOp") p') $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 joinNode
            void $ replaceWithNew q $ UnOp (Project $(v "e")) r1Node

            -- FIXME relink R2 
            |])

pullProjectFilterJoinRight :: SLRule TExpr TExpr ()
pullProjectFilterJoinRight q =
  $(dagPatMatch 'q "R1 ((q1) [SemiJoin | AntiJoin]@joinOp p (Project e (q2)))"
    [| do
        return $ do
            logRewrite "Redundant.Project.FilterJoin.Right" q
            let p' = partialEval <$> inlineJoinPredRight $(v "e") $(v "p")

            joinNode <- insert $ BinOp ($(v "joinOp") p') $(v "q1") $(v "q2")
            void $ replaceWithNew q $ UnOp R1 joinNode
            -- FIXME relink R2 
            |])

pullProjectNestJoinLeft :: SLRule TExpr TExpr ()
pullProjectNestJoinLeft q =
  $(dagPatMatch 'q "R1 ((Project e (q1)) NestJoin p (q2))"
    [| do
        return $ do
            logRewrite "Redundant.Project.NestJoin.Left" q
            let e' = partialEval $ appExprFst $(v "e")
                p' = partialEval <$> inlineJoinPredLeft $(v "e") $(v "p")

            joinNode <- insert $ BinOp (NestJoin p') $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 joinNode
            void $ replaceWithNew q $ UnOp (Project e') r1Node

            -- FIXME relink R2 and R3 parents
            |])

pullProjectNestJoinRight :: SLRule TExpr TExpr ()
pullProjectNestJoinRight q =
  $(dagPatMatch 'q "R1 ((q1) NestJoin p (Project e (q2)))"
    [| do
        return $ do
            logRewrite "Redundant.Project.NestJoin.Right" q
            let e' = partialEval $ appExprSnd $(v "e")
                p' = partialEval <$> inlineJoinPredRight $(v "e") $(v "p")

            joinNode <- insert $ BinOp (NestJoin p') $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 joinNode
            void $ replaceWithNew q $ UnOp (Project e') r1Node

            -- FIXME relink R2 and R3 parents
            |])

pullProjectThetaJoinLeft :: SLRule TExpr TExpr ()
pullProjectThetaJoinLeft q =
  $(dagPatMatch 'q "R1 ((Project e (q1)) ThetaJoin p (q2))"
    [| do
        return $ do
            logRewrite "Redundant.Project.ThetaJoin.Left" q
            let e' = partialEval $ appExprFst $(v "e")
                p' = partialEval <$> inlineJoinPredLeft $(v "e") $(v "p")

            joinNode <- insert $ BinOp (ThetaJoin p') $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 joinNode
            void $ replaceWithNew q $ UnOp (Project e') r1Node

            -- FIXME relink R2 and R3 parents
            |])

pullProjectThetaJoinRight :: SLRule TExpr TExpr ()
pullProjectThetaJoinRight q =
  $(dagPatMatch 'q "R1 ((q1) ThetaJoin p (Project e (q2)))"
    [| do
        return $ do
            logRewrite "Redundant.Project.ThetaJoin.Right" q
            let e' = partialEval $ appExprSnd $(v "e")
                p' = partialEval <$> inlineJoinPredRight $(v "e") $(v "p")

            joinNode <- insert $ BinOp (ThetaJoin p') $(v "q1") $(v "q2")
            r1Node   <- insert $ UnOp R1 joinNode
            void $ replaceWithNew q $ UnOp (Project e') r1Node

            -- FIXME relink R2 and R3 parents
            |])


pullProjectCartProductLeft :: SLRule TExpr TExpr ()
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

pullProjectCartProductRight :: SLRule TExpr TExpr ()
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


pullProjectNumber :: SLRule TExpr TExpr ()
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

pullProjectGroupAggr :: SLRule TExpr TExpr ()
pullProjectGroupAggr q =
    $(dagPatMatch 'q "GroupAggr args (Project e (q1))"
      [| do
            return $ do
                logRewrite "Redundant.Project.GroupAggr" q
                let (g, as) = $(v "args")
                    g'      = partialEval $ mergeExpr $(v "e") g
                    as'     = fmap ((partialEval . mergeExpr $(v "e")) <$>) as
                void $ replaceWithNew q $ UnOp (GroupAggr (g', as')) $(v "q1")
       |])

pullProjectSort :: SLRule TExpr TExpr ()
pullProjectSort q =
  $(dagPatMatch 'q "R1 (Sort se (Project e (q1)))"
    [| return $ do
           logRewrite "Redundant.Project.Sort" q
           let se' = partialEval $ mergeExpr $(v "e") $(v "se") 
           sortNode <- insert $ UnOp (Sort se') $(v "q1")
           r1Node   <- insert (UnOp R1 sortNode)
           void $ replaceWithNew q $ UnOp (Project $(v "e")) r1Node |])

-- Motivation: In order to eliminate or pull up sorting operations in
-- SL rewrites or subsequent stages, payload columns which might
-- induce sort order should be available as long as possible. We
-- assume that the cost of having unrequired columns around is
-- negligible (best case: column store).

pullProjectAppKey :: SLRule TExpr TExpr ()
pullProjectAppKey q =
  $(dagPatMatch 'q "(qp) AppKey (Project proj (qv))"
    [| return $ do
           logRewrite "Redundant.Project.AppKey" q
           rekeyNode <- insert $ BinOp AppKey $(v "qp") $(v "qv")
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) rekeyNode |])

pullProjectUnboxSngLeft :: SLRule TExpr TExpr ()
pullProjectUnboxSngLeft q =
  $(dagPatMatch 'q "R1 ((Project e (q1)) UnboxSng (q2))"
    [| do
         return $ do
           logRewrite "Redundant.Project.UnboxSng.Left" q

           -- Employ projection expressions on top of the unboxing
           -- operator, add right input columns.
           let e' = appExprFst $(v "e")
           unboxNode <- insert $ BinOp UnboxSng $(v "q1") $(v "q2")
           r1Node    <- insert $ UnOp R1 unboxNode

           void $ replaceWithNew q $ UnOp (Project e') r1Node |])

pullProjectUnboxDefaultLeft :: SLRule TExpr TExpr ()
pullProjectUnboxDefaultLeft q =
  $(dagPatMatch 'q "(Project e (q1)) UnboxDefault d (q2)"
    [| do
         return $ do
           logRewrite "Redundant.Project.UnboxDefault.Left" q

           -- Employ projection expressions on top of the unboxing
           -- operator, add right input columns.
           let e' = partialEval $ appExprFst $(v "e")
           unboxNode <- insert $ BinOp (UnboxDefault $(v "d")) $(v "q1") $(v "q2")

           void $ replaceWithNew q $ UnOp (Project e') unboxNode |])

pullProjectUnboxSngRight :: SLRule TExpr TExpr ()
pullProjectUnboxSngRight q =
  $(dagPatMatch 'q "R1 ((q1) UnboxSng (Project e (q2)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.UnboxSng.Right" q

           -- Preserve left input columns on top of the unboxing
           -- operator and add right input expressions with shifted
           -- columns.
           let e' = appExprSnd $(v "e")

           unboxNode <- insert $ BinOp UnboxSng $(v "q1") $(v "q2")
           r1Node    <- insert $ UnOp R1 unboxNode

           void $ replaceWithNew q $ UnOp (Project e') r1Node |])

pullProjectReplicateScalarRight :: SLRule TExpr TExpr ()
pullProjectReplicateScalarRight q =
  $(dagPatMatch 'q "R1 ((q1) ReplicateScalar (Project e (q2)))"
    [| do
         return $ do
           logRewrite "Redundant.Project.ReplicateScalar" q
           let e' = appExprSnd $(v "e")
           distNode <- insert $ BinOp ReplicateScalar $(v "q1") $(v "q2")
           r1Node   <- insert $ UnOp R1 distNode
           void $ replaceWithNew q $ UnOp (Project e') r1Node |])

pullProjectAppMap :: SLRule TExpr TExpr ()
pullProjectAppMap q =
  $(dagPatMatch 'q "R1 ((qp) [AppRep | AppSort | AppFilter]@op (Project proj (qv)))"
    [| return $ do
           logRewrite "Redundant.Project.AppMap" q
           repNode <- insert $ BinOp $(v "op") $(v "qp") $(v "qv")
           r1Node  <- insert $ UnOp R1 repNode
           void $ replaceWithNew q $ UnOp (Project $(v "proj")) r1Node |])

pullProjectMergeSegLeft :: SLRule TExpr TExpr ()
pullProjectMergeSegLeft q =
  $(dagPatMatch 'q "(Project _ (q1)) MergeSeg (q2)"
    [| return $ do
           logRewrite "Redundant.Project.MergeSeg.Left" q
           void $ replaceWithNew q $ BinOp MergeSeg $(v "q1") $(v "q2") |])

pullProjectMergeSegRight :: SLRule TExpr TExpr ()
pullProjectMergeSegRight q =
  $(dagPatMatch 'q "(q1) MergeSeg (Project e (q2))"
    [| return $ do
           logRewrite "Redundant.Project.MergeSeg.Right" q
           mergeNode <- insert $ BinOp MergeSeg $(v "q1") $(v "q2")
           void $ replaceWithNew q $ UnOp (Project $(v "e")) mergeNode |])

pullProjectUnsegment :: SLRule TExpr TExpr ()
pullProjectUnsegment q =
  $(dagPatMatch 'q "Unsegment (Project e (q1))"
     [| return $ do
           logRewrite "Redundant.Project.Unsegment" q
           segNode <- insert $ UnOp Unsegment $(v "q1")
           void $ replaceWithNew q $ UnOp (Project $(v "e")) segNode
      |]
   )

pullProjectSegment :: SLRule TExpr TExpr ()
pullProjectSegment q =
  $(dagPatMatch 'q "Segment (Project e (q1))"
     [| return $ do
           logRewrite "Redundant.Project.Segment" q
           segNode <- insert $ UnOp Segment $(v "q1")
           void $ replaceWithNew q $ UnOp (Project $(v "e")) segNode
      |]
   )

pullProjectGroupR2 :: SLRule TExpr TExpr ()
pullProjectGroupR2 q =
  $(dagPatMatch 'q "R2 (Group g (Project e (q1)))"
     [| return $ do
           logRewrite "Redundant.Project.Group.Inner" q
           let g' = partialEval $ mergeExpr $(v "e") $(v "g")
           groupNode <- insert $ UnOp (Group g') $(v "q1")
           r2Node    <- insert $ UnOp R2 groupNode
           void $ replaceWithNew q $ UnOp (Project $(v "e")) r2Node
      |]
   )

pullProjectGroupR1 :: SLRule TExpr TExpr ()
pullProjectGroupR1 q =
  $(dagPatMatch 'q "R1 (Group g (Project e (q1)))"
     [| return $ do
           logRewrite "Redundant.Project.Group.Outer" q
           let g' = partialEval $ mergeExpr $(v "e") $(v "g")
           groupNode <- insert $ UnOp (Group g') $(v "q1")
           void $ replaceWithNew q $ UnOp R1 groupNode
      |]
   )



------------------------------------------------------------------------------
-- Constant expression inputs

-- liftPairRight :: Monad m => (a, m b) -> m (a, b)
-- liftPairRight (a, mb) = mb >>= \b -> return (a, b)

-- mapPair :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
-- mapPair f g (a, b) = (f a, g b)

-- insertConstants :: [(DBCol, ScalarVal)] -> Expr -> Expr
-- insertConstants env expr =
--     case expr of
--         BinApp o e1 e2 -> BinApp o (insertConstants env e1) (insertConstants env e2)
--         UnApp o e1     -> UnApp o (insertConstants env e1)
--         Column c       -> case lookup c env of
--                                Just val -> Constant val
--                                Nothing  -> Column c
--         If c t e       -> If (insertConstants env c) (insertConstants env t) (insertConstants env e)
--         Constant _     -> expr

-- constProject :: SLRule TExpr TExpr BottomUpProps
-- constProject q =
--   $(dagPatMatch 'q "Project projs (q1)"
--     [| do
--         VProp (ConstVec constCols) <- constProp <$> properties $(v "q1")
--         let envEntry = liftPairRight . mapPair id (constVal id)
--         let constEnv = mapMaybe envEntry $ zip [1..] constCols

--         predicate $ not $ null constEnv

--         let projs' = map (insertConstants constEnv) $(v "projs")

--         -- To avoid rewriting loops, ensure that a change occured.
--         predicate $ projs' /= $(v "projs")

--         return $ do
--           logRewrite "Expr.Project.Const" q
--           void $ replaceWithNew q $ UnOp (Project projs') $(v "q1") |])
