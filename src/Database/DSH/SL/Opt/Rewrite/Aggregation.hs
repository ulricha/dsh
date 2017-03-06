{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedLists #-}

module Database.DSH.SL.Opt.Rewrite.Aggregation
    ( groupingToAggregation
    ) where

import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Opt
import           Database.DSH.Common.VectorLang
import           Database.DSH.SL.Lang
import           Database.DSH.SL.Opt.Properties.Types
import           Database.DSH.SL.Opt.Rewrite.Common

aggregationRules :: SLRuleSet TExpr TExpr ()
aggregationRules = [ inlineFoldProject ]

aggregationRulesBottomUp :: SLRuleSet TExpr TExpr BottomUpProps
aggregationRulesBottomUp = [ ]

groupingToAggregation :: SLRewrite TExpr TExpr Bool
groupingToAggregation =
    iteratively
    $ sequenceRewrites [ applyToAll inferBottomUp aggregationRulesBottomUp
                       , applyToAll noProps aggregationRules
                       ]

-- | Merge a projection into a segmented aggregate operator.
inlineFoldProject :: SLRule TExpr TExpr ()
inlineFoldProject q =
  $(dagPatMatch 'q "Fold afun (Project e (qi))"
    [| do
        let afun' = (partialEval . mergeExpr e) <$> $(v "afun")

        return $ do
            logRewrite "Aggregation.Normalize.Fold.Project" q
            void $ replaceWithNew q $ UnOp (Fold afun') $(v "qi") |])

