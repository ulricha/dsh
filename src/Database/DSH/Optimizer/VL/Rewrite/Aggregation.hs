{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.Optimizer.VL.Rewrite.Aggregation(groupingToAggregation) where

import           Control.Applicative
import           Control.Monad
import qualified Data.List.NonEmpty                         as N
import           Data.Semigroup

import           Database.Algebra.Dag.Common

import           Database.DSH.Optimizer.Common.Rewrite
import           Database.DSH.Optimizer.VL.Properties.Types
import           Database.DSH.Optimizer.VL.Rewrite.Common
import           Database.DSH.VL.Lang

aggregationRules :: VLRuleSet ()
aggregationRules = [ inlineAggrSProject
                   , inlineAggrProject
                   , inlineAggrNonEmptyProject
                   , inlineAggrSNonEmptyProject
                   , flatGrouping
                   , simpleGrouping
                   , simpleGroupingProject
                   , mergeNonEmptyAggrs
                   , mergeGroupAggr
                   , mergeGroupWithGroupAggrLeft
                   ]

aggregationRulesBottomUp :: VLRuleSet BottomUpProps
aggregationRulesBottomUp = [ nonEmptyAggr
                           , nonEmptyAggrS
                           ]

groupingToAggregation :: VLRewrite Bool
groupingToAggregation = iteratively $ sequenceRewrites [ applyToAll inferBottomUp aggregationRulesBottomUp
                                                       , applyToAll noProps aggregationRules
                                                       ]

-- FIXME this rewrite will no longer work: take the UnboxScalarS
-- operator into account.
mergeNonEmptyAggrs :: VLRule ()
mergeNonEmptyAggrs q =
  $(dagPatMatch 'q "(AggrNonEmptyS afuns1 (qi1)) Zip (AggrNonEmptyS afuns2 (qi2))"
    [| do
        predicate $ $(v "qi1") == $(v "qi2")

        return $ do
            logRewrite "Aggregation.NonEmpty.Merge" q
            let afuns  = $(v "afuns1") <> $(v "afuns2")
            let aggrOp = UnOp (AggrNonEmptyS afuns) $(v "qi1")
            void $ replaceWithNew q aggrOp |])

-- | If we can infer that the vector is not empty, we can employ a
-- simplified version of the aggregate operator that does not add a
-- default value for an empty input.
nonEmptyAggr :: VLRule BottomUpProps
nonEmptyAggr q =
  $(dagPatMatch 'q "Aggr aggrFun (q1)"
    [| do
        VProp True <- nonEmptyProp <$> properties $(v "q1")

        return $ do
            logRewrite "Aggregation.NonEmpty.Aggr" q
            let aggrOp = UnOp (AggrNonEmpty ($(v "aggrFun") N.:| [])) $(v "q1")
            void $ replaceWithNew q aggrOp |])

-- | If we can infer that all segments (if there are any) are not
-- empty, we can employ a simplified version of the aggregate operator
-- that does not add default values for empty segments.
nonEmptyAggrS :: VLRule BottomUpProps
nonEmptyAggrS q =
  $(dagPatMatch 'q "(_) AggrS aggrFun (q2)"
    [| do
        VProp True <- nonEmptyProp <$> properties $(v "q2")

        return $ do
            logRewrite "Aggregation.NonEmpty.AggrS" q
            let aggrOp = UnOp (AggrNonEmptyS ($(v "aggrFun") N.:| [])) $(v "q2")
            void $ replaceWithNew q aggrOp |])

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

-- | Merge a projection into a non-empty aggregate operator. We
-- restrict this to only one aggregate function. Therefore, merging of
-- projections must happen before merging of aggregate operators
inlineAggrNonEmptyProject :: VLRule ()
inlineAggrNonEmptyProject q =
  $(dagPatMatch 'q "AggrNonEmpty afuns (Project proj (qi))"
    [| do
        let env = zip [1..] $(v "proj")
        let afuns' = fmap (mapAggrFun (mergeExpr env)) $(v "afuns")

        return $ do
            logRewrite "Aggregation.Normalize.AggrNonEmpty.Project" q
            let aggrOp = UnOp (AggrNonEmpty afuns') $(v "qi")
            void $ replaceWithNew q aggrOp |])

-- | Merge a projection into a non-empty segmented aggregate
-- operator. We restrict this to only one aggregate
-- function. Therefore, merging of projections must happen before
-- merging of aggregate operators
inlineAggrSNonEmptyProject :: VLRule ()
inlineAggrSNonEmptyProject q =
  $(dagPatMatch 'q "AggrNonEmptyS afuns (Project proj (qi))"
    [| do
        let env = zip [1..] $(v "proj")
        let afuns' = fmap (mapAggrFun (mergeExpr env)) $(v "afuns")

        return $ do
            logRewrite "Aggregation.Normalize.AggrNonEmptyS.Project" q
            let aggrOp = UnOp (AggrNonEmptyS afuns') $(v "qi")
            void $ replaceWithNew q aggrOp |])


-- If grouping is performed by simple scalar expressions, we can
-- employ a simpler operator.
simpleGrouping :: VLRule ()
simpleGrouping q =
  $(dagPatMatch 'q "(Project projs (q1)) Group (q2)"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Aggregation.Grouping.ScalarS" q
          void $ replaceWithNew q $ UnOp (GroupScalarS $(v "projs")) $(v "q1") |])

-- If grouping is performed by simple scalar expressions, we can
-- employ a simpler operator. This dagPatMatch arises when the grouping
-- input projection (left) is merged with the common origin of left
-- and right groupby input.
simpleGroupingProject :: VLRule ()
simpleGroupingProject q =
  $(dagPatMatch 'q "R2 (qg=(Project projs1 (q1)) Group (Project projs2 (q2)))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        return $ do
          logRewrite "Aggregation.Grouping.ScalarS.Project" q

          -- Add the grouping columns to the group input projection
          let projs = $(v "projs2") ++ $(v "projs1")
          projectNode <- insert $ UnOp (Project projs) $(v "q1")

          let groupExprs = [ Column $ i + length $(v "projs2")
                           | i <- [1 .. length $(v "projs1")]
                           ]

          -- group by the columns that have been added to the input
          -- projection.
          groupNode <- insert $ UnOp (GroupScalarS groupExprs) projectNode

          -- Remove the additional grouping columns from the inner vector
          r2Node <- insert $ UnOp R2 groupNode
          let origSchemaProj = map Column [1 .. length $(v "projs2")]
          topProjectNode <- insert $ UnOp (Project origSchemaProj) r2Node
          replace q topProjectNode

          -- Re-wire R1 and R3 parents of the group operator
          replace $(v "qg") groupNode |])

-- We rewrite a combination of GroupBy and aggregation operators into a single
-- VecAggr operator if the following conditions hold:
--
-- 1. The R2 output of GroupBy is only consumed by aggregation operators (MaxL,
--    MinL, VecSumL, LengthSeg)
-- 2. The grouping criteria is a simple column projection from the input vector
flatGrouping :: VLRule ()
flatGrouping q =
  $(dagPatMatch 'q "AggrNonEmptyS afuns (R2 (GroupScalarS groupExprs (q1)))"
    [| do

        return $ do
          logRewrite "Aggregation.Grouping.Aggr" q
          -- The output format of the new VecAggr operator is
          -- [p1, ..., pn, a1, ..., am] where p1, ..., pn are the
          -- grouping columns and a1, ..., am are the aggregates
          -- themselves.
          -- For the moment, we keep only the aggregate output and discard the
          -- grouping columns. They have to be added later on.

          let gw = length $(v "groupExprs")
              aw = N.length $(v "afuns")
              proj = map Column [gw + 1.. aw + gw]

          -- We obviously assume that the grouping columns are still present in
          -- the right input of GroupBy at the same position. In combination
          -- with rewrite pushExprThroughGroupBy, this is true since we only
          -- add columns at the end.
          groupNode <- insert $ UnOp (GroupAggr ($(v "groupExprs"), $(v "afuns"))) $(v "q1")
          void $ replaceWithNew q $ UnOp (Project proj) groupNode |])

mergeGroupAggr :: VLRule ()
mergeGroupAggr q =
  $(dagPatMatch 'q "(GroupAggr args1 (q1)) Zip (GroupAggr args2 (q2))"
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
-- aggregates have already been merged with GroupScalarS into
-- GroupAggr. If the GroupAggr output is combined with the R1 output
-- of GroupScalarS on the same input and grouping expressions via Zip,
-- the effect is that only the grouping expressions are duplicated.
mergeGroupWithGroupAggrLeft :: VLRule ()
mergeGroupWithGroupAggrLeft q =
  $(dagPatMatch 'q "(R1 (GroupScalarS ges (q1))) Zip (GroupAggr args (q2))"
    [| do
        let (ges', afuns) = $(v "args")
    
        -- Input vectors and grouping expressions have to be the same.
        predicate $ $(v "q1") == $(v "q2")
        predicate $ $(v "ges") == ges'

        return $ do
            logRewrite "Aggregation.Normalize.MergeGroupScalars" q
            
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
                     

