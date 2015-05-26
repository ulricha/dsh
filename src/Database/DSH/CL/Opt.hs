-- | This module performs optimizations on the Comprehension Language
-- (CL).
module Database.DSH.CL.Opt
  ( optimizeComprehensions
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
    <+ repeatR nestjoinR
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
    (guardpushbackR
        >+> repeatR introduceCartProductsR
        >+> repeatR predpushdownR)

postProcessR :: RewriteC CL
postProcessR = repeatR $ anybuR postProcessCompR

--------------------------------------------------------------------------------
-- Rewrite Strategy

-- | Perform a top-down traversal of a query expression, looking for
-- rewrite opportunities on comprehensions and other expressions.
descendR :: RewriteC CL
descendR = readerT $ \cl -> case cl of

    ExprCL Comp{} -> optCompR

    -- On non-comprehensions, try to apply partial evaluation rules
    -- before descending
    ExprCL _      -> repeatR partialEvalR
                     >+> repeatR normalizeExprR
                     >+> anyR descendR

    -- We are looking only for expressions. On non-expressions, simply descend.
    _             -> anyR descendR


-- | Optimize single comprehensions during a top-down traversal
optCompR :: RewriteC CL
optCompR = do
    Comp{} <- promoteT idR
    -- debugPretty "optCompR at" c

    repeatR (compNormEarlyR
             <+ predpushdownR
             <+ flatjoinsR
             <+ anyR descendR
             ) >>> debugShow "after comp"

applyOptimizationsR :: RewriteC CL
applyOptimizationsR = descendR >+> anytdR loopInvariantR >+> anybuR buUnnestR

optimizeR :: RewriteC CL
optimizeR = resugarR >+>
            normalizeOnceR >+>
            repeatR applyOptimizationsR >+>
            postProcessR

-- | Apply the default set of unnesting and decorrelation rewrites to
-- a CL query.
optimizeComprehensions :: Expr -> Expr
optimizeComprehensions expr =
    case applyExpr (optimizeR >>> projectT) expr of
        Left _      -> expr
        Right expr' -> expr'
