{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE LambdaCase          #-}
    
-- | This module performs optimizations on the Comprehension Language (CL).
module Database.DSH.CL.Opt 
  ( optimizeComprehensions ) where
  
import Control.Arrow
       
import Database.DSH.CL.Lang
import Database.DSH.CL.Kure

import Database.DSH.CL.Opt.Aux
import Database.DSH.CL.Opt.Support
import Database.DSH.CL.Opt.PredPushdown
import Database.DSH.CL.Opt.Normalize
import Database.DSH.CL.Opt.PartialEval
import Database.DSH.CL.Opt.CompNormalization
import Database.DSH.CL.Opt.FlatJoin
import Database.DSH.CL.Opt.NestJoin

--------------------------------------------------------------------------------
-- Rewrite Strategy: Rule Groups

-- FIXME add m_norm_1R once tables for benchmark queries exist
-- | Comprehension normalization rules 1 to 3.
compNormEarlyR :: RewriteC CL
compNormEarlyR = m_norm_1R {- <+ m_norm_2R -} <+ m_norm_3R

-- | Comprehension normalization rules 4 and 5. Beware: these rewrites should
-- propably occur late in the chain, as they might prohibit semijoin/antijoin
-- introduction
compNormLateR :: RewriteC CL
compNormLateR = m_norm_4R <+ m_norm_5R

buUnnestR :: RewriteC CL
buUnnestR = 
    zipCorrelatedR 
    <+ repeatR nestjoinR 
    -- If the inverse M-Norm-3 succeeds, try to unnest the new
    -- generator
    <+ (nestingGenR >>> pathR [CompQuals, QualsSingleton, BindQualExpr] nestjoinR)
   
--------------------------------------------------------------------------------
-- Rewrite Strategy

-- | Perform a top-down traversal of a query expression, looking for
-- rewrite opportunities on comprehensions and other expressions.
descendR :: RewriteC CL
descendR = readerT $ \case

    ExprCL (Comp _ _ _) -> optCompR

    -- On non-comprehensions, try to clean up before descending
    ExprCL _            -> repeatR (onetdR partialEvalR) >+> anyR descendR

    -- We are looking only for expressions. On non-expressions, simply descend.
    _                   -> anyR descendR


-- | Optimize single comprehensions during a top-down traversal
optCompR :: RewriteC CL
optCompR = do
    c@(Comp _ _ _) <- promoteT idR
    debugPretty "optCompR at" c

    repeatR $ do
          -- e <- promoteT idR
          -- debugPretty "comp at" (e :: Expr)
          (normalizeAlwaysR
             <+ compNormEarlyR
             <+ predpushdownR
             <+ flatjoinsR
             <+ anyR descendR
             ) >>> debugShow "after comp"
            
optimizeR :: RewriteC CL
optimizeR = normalizeOnceR >+> repeatR (descendR >+> anybuR buUnnestR >+> anytdR factorConstantPredsR)
        
optimizeComprehensions :: Expr -> Expr
optimizeComprehensions expr = {- trace ("(depth, count) "++ show (depth expr)) $ -} debugOpt expr optimizedExpr

  where
    -- optimizedExpr = applyExpr (strategy >>> projectT) expr
    -- optimizedExpr = applyExpr (test >>> projectT) expr
    optimizedExpr = applyExpr (optimizeR >>> projectT) expr
