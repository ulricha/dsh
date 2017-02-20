-- | This module performs optimizations on the Comprehension Language
-- (CL).
module Database.DSH.CL.Opt
  ( optBU
  , optimizeComprehensions
  , optTD
  , optFlat
  , optResugar
  , CLOptimizer
  ) where

import           Control.Arrow

import           Database.DSH.Common.Pretty

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang

import           Database.DSH.CL.Opt.Auxiliary
import           Database.DSH.CL.Opt.CompNormalization
import           Database.DSH.CL.Opt.FlatJoin
import           Database.DSH.CL.Opt.GroupJoin
import           Database.DSH.CL.Opt.JoinPushdown
import           Database.DSH.CL.Opt.LetFloating
import           Database.DSH.CL.Opt.LoopInvariant
import           Database.DSH.CL.Opt.NestJoin
import           Database.DSH.CL.Opt.Normalize
import           Database.DSH.CL.Opt.PartialEval
import           Database.DSH.CL.Opt.PredPushdown
import           Database.DSH.CL.Opt.ProjectionPullup
import           Database.DSH.CL.Opt.Resugar

--------------------------------------------------------------------------------
-- Rewrite Strategy: Rule Groups

-- | Comprehension normalization rules 1 to 3.
compNormEarlyR :: RewriteC CL
compNormEarlyR =    m_norm_1R
                 <+ m_norm_2R
                 <+ m_norm_3R
                 -- Does not lead to good code. See lablog entry (24.11.2014)
                 -- <+ invariantguardR
                 <+ ifgeneratorR
                 <+ identityCompR

-- | Nestjoin rewrites are applied bottom-up. Innermost nesting opportunities
-- must be dealt with first in order to produce trees of nesting operators.
decorrelateNestingR :: RewriteC CL
decorrelateNestingR =
    zipCorrelatedR
    <+ repeatR (nestjoinR >+> groupjoinR >+> anytdR optimizeGroupJoinR)
    -- If the inverse M-Norm-3 succeeds, try to unnest the new
    -- generator
    -- <+ (nestingGenR >>> pathR [CompQuals, QualsSingleton, BindQualExpr] nestjoinR)

--------------------------------------------------------------------------------
-- Post-processing of queries.
--
-- This rule group consists of cleanup rewrites that are applied once at the end
-- of rewriting.

-- | Normalize unnested comprehensions. To avoid nested iterators
-- after desugaring whenever possible, consecutive generators that do
-- not depend on each other are mapped to cartesian products. After
-- that, we try to push guards down into product inputs.
postProcessCompR :: RewriteC CL
postProcessCompR = do
    ExprCL Comp{} <- idR
    guardpushbackR
        -- >+> repeatR introduceCartProductsR
        >+> repeatR predpushdownR

postProcessOnceR :: RewriteC CL
postProcessOnceR = anybuR sidewaysR

postProcessLoopR :: RewriteC CL
postProcessLoopR = anybuR (postProcessCompR <+ joinPushdownR)

postProcessR :: RewriteC CL
postProcessR = repeatR postProcessLoopR >+> postProcessOnceR >+> postProcessLoopR

--------------------------------------------------------------------------------

-- | Perform a top-down traversal of a query expression, looking for rewrite
-- opportunities on comprehensions and other expressions: comprehension
-- unnesting, flat join introduction, partial evaluation.
descendR :: RewriteC CL
descendR = readerT $ \cl -> case cl of

    ExprCL Comp{} ->
        repeatR ( compNormEarlyR
                  <+ predpushdownR
                  <+ flatjoinsR
                  <+ anyR descendR
                )

    -- On non-comprehensions, try to apply partial evaluation rules
    -- before descending
    ExprCL _      -> repeatR partialEvalLogR
                     >+> repeatR normalizeExprR
                     >+> pullProjectionR
                     >+> optimizeGroupJoinR
                     >+> anyR descendR

    -- We are looking only for expressions. On non-expressions, simply descend.
    _             -> anyR descendR

--------------------------------------------------------------------------------
-- Rewrite Strategies

mainOptTD :: RewriteC CL
mainOptTD = repeatR descendR >+> anytdR loopInvariantR >+> anybuR floatBindingsR >+> onetdR decorrelateNestingR

mainOptBU :: RewriteC CL
mainOptBU = repeatR descendR >+> anytdR loopInvariantR >+> anybuR floatBindingsR >+> anybuR decorrelateNestingR

mainOptFlatR :: RewriteC CL
mainOptFlatR = repeatR descendR >+> anytdR loopInvariantR >+> anybuR floatBindingsR

-- | The complete optimization pipeline
optPipelineR :: RewriteC CL -> RewriteC CL
optPipelineR mainOptR = normalizeOnceR >+> repeatR mainOptR >+> postProcessR

--------------------------------------------------------------------------------
-- CL Optimizers

-- | A optimizer that transforms a CL expression. Returns the potentially
-- modified expression and a rewriting log.
type CLOptimizer = Expr -> (Expr, String)

mkOptimizer :: RewriteC CL -> CLOptimizer
mkOptimizer opt expr =
    case applyExprLog ((resugarR >+> opt) >>> projectT) expr of
        Left _                    -> (expr, "")
        Right (expr', rewriteLog) ->
            case applyExpr (resugarR) expr of
                Left _        -> (expr', rewriteLog)
                Right (ExprCL exprSug) -> (expr', pp (exprSug::Expr) ++ "\n" ++ rewriteLog)
                _ -> undefined

-- | Apply the default set of unnesting and decorrelation rewrites to
-- a CL query. Nestjoins are introduced bottom-up.
optBU :: CLOptimizer
optBU = mkOptimizer $ optPipelineR mainOptBU

optimizeComprehensions :: CLOptimizer
optimizeComprehensions = optBU

-- | Apply the default set of unnesting and decorrelation rewrites to
-- a CL query. Nestjoins are introduced top-down.
optTD :: CLOptimizer
optTD = mkOptimizer $ optPipelineR mainOptTD

-- | CL optimizer: normalize and introduce flat joins.
optFlat :: CLOptimizer
optFlat = mkOptimizer $ optPipelineR mainOptFlatR

-- | CL optimizer: Resugar comprehensions
optResugar :: CLOptimizer
optResugar = mkOptimizer idR
