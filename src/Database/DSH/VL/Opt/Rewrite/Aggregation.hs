{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.VL.Opt.Rewrite.Aggregation
    ( groupingToAggregation
    ) where

import           Control.Monad
import qualified Data.List.NonEmpty                   as N
import           Data.Semigroup

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Opt
import           Database.DSH.VL.Lang
import           Database.DSH.VL.Opt.Properties.Types
import           Database.DSH.VL.Opt.Rewrite.Common

aggregationRules :: VLRuleSet ()
aggregationRules = [ inlineAggrSProject
                   , inlineAggrProject
                   , flatGrouping
                   , mergeGroupAggrAggrS
                   -- , mergeNonEmptyAggrs
                   , mergeGroupAggr
                   , mergeGroupWithGroupAggrLeft
                   , mergeGroupWithGroupAggrRight
                   , groupJoin
                   ]

aggregationRulesBottomUp :: VLRuleSet BottomUpProps
aggregationRulesBottomUp = [ {- nonEmptyAggr
                           , nonEmptyAggrS -}
                           ]

groupingToAggregation :: VLRewrite Bool
groupingToAggregation =
    iteratively
    $ sequenceRewrites [ applyToAll inferBottomUp aggregationRulesBottomUp
                       , applyToAll noProps aggregationRules
                       ]

-- -- FIXME this rewrite will no longer work: take the UnboxSngS
-- -- operator into account.
-- mergeNonEmptyAggrs :: VLRule ()
-- mergeNonEmptyAggrs q =
--   $(dagPatMatch 'q "(AggrNonEmptyS afuns1 (qi1)) Zip (AggrNonEmptyS afuns2 (qi2))"
--     [| do
--         predicate $ $(v "qi1") == $(v "qi2")

--         return $ do
--             logRewrite "Aggregation.NonEmpty.Merge" q
--             let afuns  = $(v "afuns1") <> $(v "afuns2")
--             let aggrOp = UnOp (AggrNonEmptyS afuns) $(v "qi1")
--             void $ replaceWithNew q aggrOp |])

-- -- | If we can infer that the vector is not empty, we can employ a
-- -- simplified version of the aggregate operator that does not add a
-- -- default value for an empty input.
-- nonEmptyAggr :: VLRule BottomUpProps
-- nonEmptyAggr q =
--   $(dagPatMatch 'q "Aggr aggrFun (q1)"
--     [| do
--         VProp True <- nonEmptyProp <$> properties $(v "q1")

--         return $ do
--             logRewrite "Aggregation.NonEmpty.Aggr" q
--             let aggrOp = UnOp (AggrNonEmpty ($(v "aggrFun") N.:| [])) $(v "q1")
--             void $ replaceWithNew q aggrOp |])

-- -- | If we can infer that all segments (if there are any) are not
-- -- empty, we can employ a simplified version of the aggregate operator
-- -- that does not add default values for empty segments.
-- nonEmptyAggrS :: VLRule BottomUpProps
-- nonEmptyAggrS q =
--   $(dagPatMatch 'q "(_) AggrS aggrFun (q2)"
--     [| do
--         VProp True <- nonEmptyProp <$> properties $(v "q2")

--         return $ do
--             logRewrite "Aggregation.NonEmpty.AggrS" q
--             let aggrOp = UnOp (AggrNonEmptyS ($(v "aggrFun") N.:| [])) $(v "q2")
--             void $ replaceWithNew q aggrOp |])

-- | Merge a projection into a segmented aggregate operator.
inlineAggrProject :: VLRule ()
inlineAggrProject q =
  $(dagPatMatch 'q "Aggr afun (Project proj (qi))"
    [| do
        let env = zip [1..] $(v "proj")
        let afun' = mapAggrFun (mergeExpr env) $(v "afun")

        return $ do
            logRewrite "Aggregation.Normalize.Aggr.Project" q
            void $ replaceWithNew q $ UnOp (Aggr afun') $(v "qi") |])

-- | Merge a projection into a segmented aggregate operator.
inlineAggrSProject :: VLRule ()
inlineAggrSProject q =
  $(dagPatMatch 'q "(qo) AggrS afun (Project proj (qi))"
    [| do
        let env = zip [1..] $(v "proj")
        let afun' = mapAggrFun (mergeExpr env) $(v "afun")

        return $ do
            logRewrite "Aggregation.Normalize.AggrS.Project" q
            void $ replaceWithNew q $ BinOp (AggrS afun') $(v "qo") $(v "qi") |])

-- | We rewrite a combination of GroupS and aggregation operators into a single
-- GroupAggr operator.
flatGrouping :: VLRule ()
flatGrouping q =
  $(dagPatMatch 'q "R1 (qu=(qr1=R1 (qg)) UnboxSng ((_) AggrS afun (R2 (qg1=GroupS groupExprs (q1)))))"
    [| do

        -- Ensure that the aggregate results are unboxed using the
        -- outer vector of the grouping operator.
        predicate $ $(v "qg") == $(v "qg1")

        return $ do
          logRewrite "Aggregation.Grouping.Aggr" q
          let afuns = $(v "afun") N.:| []

          groupAggrNode <- insert $ UnOp (GroupAggr ($(v "groupExprs"), afuns)) $(v "q1")
          replace q groupAggrNode
          let proj = map Column [1..length $(v "groupExprs")]
          void $ replaceWithNew $(v "qr1") $ UnOp (Project proj) groupAggrNode
        |])

-- | Cleanup rewrite: merge a segment aggregate with a group
-- operator. In contrast to rewrite 'flatGrouping", unboxing is performed using
-- a GroupAggr operator that has the same grouping expressions as the original
-- grouping. As both Group and GroupAggr use the grouping expressions on the
-- same input, we add the aggregate to the list of GroupAggr aggregates and use
-- only the GroupAggr operator.
--
-- This pattern can occur if R1 outputs of Group are moved to a
-- GroupAggr and segment aggregate and unboxing operators are pushed
-- down through segment propagation operators.
--
-- Testcase: TPC-H Q11, Q15
mergeGroupAggrAggrS :: VLRule ()
mergeGroupAggrAggrS q =
  $(dagPatMatch 'q "R1 (qu=(qg=GroupAggr args (q1)) UnboxSng ((_) AggrS afun (R2 (qg1=GroupS groupExprs (q2)))))"
    [| do
        predicate $ $(v "q1") == $(v "q2")
        let (groupExprs', afuns) = $(v "args")
        predicate $ groupExprs' == $(v "groupExprs")

        return $ do
          logRewrite "Aggregation.Grouping.Aggr2" q

          let afunsCombined = afuns <> (pure $(v "afun"))
          groupAggrNode <- insert $ UnOp (GroupAggr ($(v "groupExprs"), afunsCombined)) $(v "q1")
          replace q groupAggrNode

          -- Take care not to have duplicates of the grouping operator: Re-Wire
          -- all parents of the original GroupAggr operator to the new
          -- (extended) one and use a projection to keep the original schema.
          gaParents <- filter (/= $(v "qu")) <$> parents $(v "qg")
          let proj = map Column [1..(length groupExprs' + length afuns)]
          projNode <- insert $ UnOp (Project proj) groupAggrNode
          forM_ gaParents $ \p -> replaceChild p $(v "qg") projNode
    |])

mergeGroupAggr :: VLRule ()
mergeGroupAggr q =
  $(dagPatMatch 'q "(GroupAggr args1 (q1)) Align (GroupAggr args2 (q2))"
    [| do
        let (ges1, afuns1) = $(v "args1")
        let (ges2, afuns2) = $(v "args2")

        -- The rewrite can be applied if the same input is grouped
        -- according to the same grouping expressions.
        predicate $ ges1 == ges2
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Aggregation.Normalize.MergeGroupAggr" q
          groupNode <- insert $ UnOp (GroupAggr ($(v "ges1"), ($(v "afuns1") <> $(v "afuns2")))) $(v "q1")

          -- Reconstruct the schema produced by Zip. Note that this
          -- duplicates the grouping columns.
          let groupWidth = length $(v "ges1")
              aggrWidth1 = N.length afuns1
              aggrWidth2 = N.length afuns2
              groupCols  = [ Column c | c <- [1 .. groupWidth]]

          let proj = groupCols
                     ++
                     [ Column $ c + groupWidth | c <- [1 .. aggrWidth1] ]
                     ++
                     groupCols
                     ++
                     [ Column $ c + groupWidth + aggrWidth1 | c <- [1 .. aggrWidth2] ]

          void $ replaceWithNew q $ UnOp (Project proj) groupNode |])

-- | This is a cleanup rewrite: It applies in a situation when
-- aggregates have already been merged with Group into GroupAggr. If
-- the GroupAggr output is combined with the R1 output of Group on the
-- same input and grouping expressions via Align, the effect is that
-- only the grouping expressions are duplicated.
mergeGroupWithGroupAggrLeft :: VLRule ()
mergeGroupWithGroupAggrLeft q =
  $(dagPatMatch 'q "(R1 (GroupS ges (q1))) Align (GroupAggr args (q2))"
    [| do
        let (ges', afuns) = $(v "args")

        -- Input vectors and grouping expressions have to be the same.
        predicate $ $(v "q1") == $(v "q2")
        predicate $ $(v "ges") == ges'

        return $ do
            logRewrite "Aggregation.Normalize.MergeGroup.Left" q

            -- To keep the schema, we have to duplicate the grouping
            -- columns.
            let groupWidth = length ges'
                aggrWidth  = N.length afuns
                groupCols  = [ Column c | c <- [1..groupWidth] ]
                proj       = groupCols
                             ++
                             groupCols
                             ++
                             [ Column $ c + groupWidth | c <- [1..aggrWidth] ]

            groupNode <- insert $ UnOp (GroupAggr (ges', afuns)) $(v "q1")
            void $ replaceWithNew q $ UnOp (Project proj) groupNode |])

-- | The mirrored dual of rewrite
-- 'Aggregation.Normalize.MergeGroup.Left'.
mergeGroupWithGroupAggrRight :: VLRule ()
mergeGroupWithGroupAggrRight q =
  $(dagPatMatch 'q "(GroupAggr args (q1)) Align (R1 (GroupS ges (q2)))"
    [| do
        let (ges', afuns) = $(v "args")

        -- Input vectors and grouping expressions have to be the same.
        predicate $ $(v "q1") == $(v "q2")
        predicate $ $(v "ges") == ges'

        return $ do
            logRewrite "Aggregation.Normalize.MergeGroup.Right" q

            -- To keep the schema, we have to duplicate the grouping
            -- columns.
            let groupWidth = length ges'
                aggrWidth  = N.length afuns
                groupCols  = [ Column c | c <- [1..groupWidth] ]
                proj       = groupCols
                             ++
                             [ Column $ c + groupWidth | c <- [1..aggrWidth] ]
                             ++
                             groupCols

            groupNode <- insert $ UnOp (GroupAggr (ges', afuns)) $(v "q1")
            void $ replaceWithNew q $ UnOp (Project proj) groupNode |])

-- | Merge nestjoin-based binary grouping and subsequent aggregation
-- into one groupjoin operator.
groupJoin :: VLRule ()
groupJoin q =
  $(dagPatMatch 'q "R1 ((qo) UnboxSng ((qo1) AggrS a (R1 ((qo2) NestJoin p (qi)))))"
    [| do
        predicate $ $(v "qo1") == $(v "qo")
        predicate $ $(v "qo2") == $(v "qo")

        return $ do
            logRewrite "GroupJoin" q
            void $ replaceWithNew q $ BinOp (GroupJoin ($(v "p"), $(v "a"))) $(v "qo") $(v "qi")
        |])
