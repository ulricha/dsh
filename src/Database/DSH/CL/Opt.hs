-- | This module performs optimizations on the Comprehension Language
-- (CL).
module Database.DSH.CL.Opt
  ( optimizeComprehensions
  , resugarComprehensions
  , normalizeComprehensions
  , identityComprehensions
  ) where

import           Control.Arrow

import           Database.DSH.Common.Kure

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang

import           Database.DSH.CL.Opt.Auxiliary
import           Database.DSH.CL.Opt.CompNormalization
import           Database.DSH.CL.Opt.FlatJoin
import           Database.DSH.CL.Opt.LoopInvariant
import           Database.DSH.CL.Opt.NestJoin
import           Database.DSH.CL.Opt.Normalize
import           Database.DSH.CL.Opt.PartialEval
import           Database.DSH.CL.Opt.PostProcess
import           Database.DSH.CL.Opt.PredPushdown
import           Database.DSH.CL.Opt.Resugar
import           Database.DSH.CL.Opt.JoinPushdown
import           Database.DSH.CL.Opt.GroupJoin
import           Database.DSH.CL.Opt.ProjectionPullup

--------------------------------------------------------------------------------
-- Rewrite Strategy: Rule Groups

-- | Comprehension normalization rules 1 to 3.
compNormEarlyR :: RewriteC CL
compNormEarlyR = m_norm_1R
                 <+ m_norm_2R
                 <+ m_norm_3R
                 -- Does not lead to good code. See lablog entry (24.11.2014)
                 -- <+ invariantguardR
                 <+ ifgeneratorR
                 <+ identityCompR

-- | Nestjoin/Nestproduct rewrites are applied bottom-up. Innermost
-- nesting opportunities must be dealt with first in order to produce
-- trees of nesting operators.
buUnnestR :: RewriteC CL
buUnnestR =
    zipCorrelatedR
    <+ repeatR (nestjoinR >+> groupjoinR >+> anytdR optimizeGroupJoinR)
    -- If the inverse M-Norm-3 succeeds, try to unnest the new
    -- generator
    <+ (nestingGenR >>> pathR [CompQuals, QualsSingleton, BindQualExpr] nestjoinR)

-- | Normalize unnested comprehensions. To avoid nested iterators
-- after desugaring whenever possible, consecutive generators that do
-- not depend on each other are mapped to cartesian products. After
-- that, we try to push guards down into product inputs.
postProcessCompR :: RewriteC CL
postProcessCompR = do
    ExprCL Comp{} <- idR
    guardpushbackR
        >+> repeatR introduceCartProductsR
        >+> repeatR predpushdownR

postProcessOnceR :: RewriteC CL
postProcessOnceR = anybuR sidewaysR

postProcessLoopR :: RewriteC CL
postProcessLoopR = anybuR (postProcessCompR <+ joinPushdownR)

postProcessR :: RewriteC CL
postProcessR = repeatR postProcessLoopR >+> postProcessOnceR >+> postProcessLoopR

--------------------------------------------------------------------------------
-- Rewrite Strategy

-- | Perform a top-down traversal of a query expression, looking for
-- rewrite opportunities on comprehensions and other expressions.
descendR :: RewriteC CL
descendR = readerT $ \cl -> case cl of

    ExprCL Comp{} ->
        repeatR (compNormEarlyR
                 <+ predpushdownR
                 <+ flatjoinsR
                 <+ anyR descendR
                ) >>> debugShow "after comp"

    -- On non-comprehensions, try to apply partial evaluation rules
    -- before descending
    ExprCL _      -> repeatR partialEvalR
                     >+> repeatR normalizeExprR
                     >+> pullProjectionR
                     >+> optimizeGroupJoinR
                     >+> anyR descendR

    -- We are looking only for expressions. On non-expressions, simply descend.
    _             -> anyR descendR

applyOptimizationsR :: RewriteC CL
applyOptimizationsR = repeatR descendR >+> anytdR loopInvariantR >+> anybuR buUnnestR

normalizeFlatR :: RewriteC CL
normalizeFlatR = resugarR >+> normalizeOnceR >+> repeatR (repeatR descendR >+> anytdR loopInvariantR)

-- | The complete optimization pipeline
optimizeR :: RewriteC CL
optimizeR = resugarR >+>
            normalizeOnceR >+>
            repeatR applyOptimizationsR >+>
            postProcessR

--------------------------------------------------------------------------------

-- | Apply the default set of unnesting and decorrelation rewrites to
-- a CL query.
optimizeComprehensions :: Expr -> Expr
optimizeComprehensions expr =
    case applyExpr (optimizeR >>> projectT) expr of
        Left _      -> expr
        Right expr' -> expr'

-- | CL optimizer: normalize and introduce flat joins.
normalizeComprehensions :: Expr -> Expr
normalizeComprehensions expr = 
    case applyExpr (normalizeFlatR >>> projectT) expr of
        Left _      -> expr
        Right expr' -> expr'

-- | Identity CL optimizer
identityComprehensions :: Expr -> Expr
identityComprehensions = id

-- | CL optimizer: Resugar comprehensions
resugarComprehensions :: Expr -> Expr
resugarComprehensions expr =
    case applyExpr (resugarR >>> projectT) expr of
        Left _      -> expr
        Right expr' -> expr'
