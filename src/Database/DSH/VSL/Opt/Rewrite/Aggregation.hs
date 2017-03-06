{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VSL.Opt.Rewrite.Aggregation
    ( groupingToAggregation
    ) where

import           Control.Monad

import           Database.Algebra.Dag.Common

-- import           Database.DSH.Common.Lang
import           Database.DSH.Common.Opt
import           Database.DSH.Common.VectorLang
import           Database.DSH.VSL.Lang
import           Database.DSH.VSL.Opt.Properties.Types
import           Database.DSH.VSL.Opt.Rewrite.Common

aggregationRules :: VSLRuleSet TExpr TExpr ()
aggregationRules = [ inlineFoldProject ]

aggregationRulesBottomUp :: VSLRuleSet TExpr TExpr BottomUpProps
aggregationRulesBottomUp = []

groupingToAggregation :: VSLRewrite TExpr TExpr Bool
groupingToAggregation =
    iteratively
    $ sequenceRewrites [ applyToAll inferBottomUp aggregationRulesBottomUp
                       , applyToAll noProps aggregationRules
                       ]

-- | Merge a projection into a segmented aggregate operator.
inlineFoldProject :: VSLRule TExpr TExpr ()
inlineFoldProject q =
  $(dagPatMatch 'q "Fold afun (Project e (qi))"
    [| do
        let afun' = (partialEval . mergeExpr e) <$> $(v "afun")

        return $ do
            logRewrite "Aggregation.Normalize.Fold.Project" q
            void $ replaceWithNew q $ UnOp (Fold afun') $(v "qi") |])
