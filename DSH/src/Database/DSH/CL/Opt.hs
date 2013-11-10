{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE LambdaCase          #-}
    
-- | This module performs optimizations on the Comprehension Language (CL).
module Database.DSH.CL.Opt 
  ( opt ) where
  
import Control.Arrow

import Database.DSH.CL.Lang
import Database.DSH.CL.Kure

import Database.DSH.CL.Opt.Aux
import Database.DSH.CL.Opt.Support
import Database.DSH.CL.Opt.Normalize
import Database.DSH.CL.Opt.CompNormalization
import Database.DSH.CL.Opt.FlatJoin
import Database.DSH.CL.Opt.NestJoin
import Database.DSH.CL.Opt.Operators

--------------------------------------------------------------------------------
-- Rewrite Strategy: Rule Groups

-- Clean up remains and perform partial evaluation on the current node
cleanupR :: RewriteC CL
cleanupR = (extractR partialEvalR <+ extractR houseCleaningR <+ normalizeR) 
           >>> debugShow "after cleanup"

flatJoinsR :: RewriteC CL
flatJoinsR = (promoteR (tryR pushSemiFilters) >>> semijoinR >>> debugTrace "semijoin")
            <+ (promoteR (tryR pushAntiFilters) >>> antijoinR >>> debugTrace "antijoin")
            <+ (promoteR (tryR pushEquiFilters) >>> eqjoinR >>> debugTrace "equijoin")
            
-- FIXME add m_norm_1R once tables for benchmark queries exist
-- | Comprehension normalization rules 1 to 3.
compNormEarlyR :: RewriteC CL
compNormEarlyR = m_norm_2R <+ m_norm_3R

-- | Comprehension normalization rules 4 and 5. Beware: these rewrites should
-- propably occur late in the chain, as they might prohibit semijoin/antijoin
-- introduction
compNormLateR :: RewriteC CL
compNormLateR = m_norm_4R <+ m_norm_5R
           
nestJoinsR :: RewriteC CL
nestJoinsR = ((nestjoinHeadR >>> tryR cleanupNestJoinR) >>> debugTrace "nestjoinhead")
             <+ (nestjoinGuardR >>> debugTrace "nestjoinguard")
            
  where
    cleanupNestJoinR :: RewriteC CL
    -- FIXME OPT anytdR could go away. combineNestJoinsR matches either the
    -- current expression or the second child expression (when head was factored
    -- out, i.e. a map introduced).
    cleanupNestJoinR = repeatR $ anytdR (combineNestJoinsR >>> debugTrace "combinenestjoins")

--------------------------------------------------------------------------------
-- Rewrite Strategy
            
optimizeR :: RewriteC CL
optimizeR = normalizeR >+> repeatR (descendR >+> anybuR nestJoinsR)
  where
    descendR :: RewriteC CL
    descendR = readerT $ \case

        ExprCL (Comp _ _ _) -> optCompR

        -- On non-comprehensions, try to clean up before descending
        ExprCL _            -> repeatR (onetdR cleanupR) >+> anyR descendR

        -- We are looking only for expressions. On non-expressions, simply descend.
        _                   -> anyR descendR


    optCompR :: RewriteC CL
    optCompR = do
        c@(Comp _ _ _) <- promoteT idR
        debugUnit "optCompR at" c

        repeatR $ do
            -- e <- promoteT idR
            -- debugUnit "comp at" (e :: Expr)
              (compNormEarlyR
                 <+ (promoteR (tryR pushSimpleFilters) >>> selectR isSimplePred)
                 <+ flatJoinsR
                 <+ anyR descendR
                 {- <+ nestJoinsR -}) >>> debugShow "after comp"
        
{-
-- debug function
depth :: Expr -> (Int, Int)
depth e = (maximum ps, length ps)
  where ps = map length $ either (const []) id $ applyExpr (collectT rootPathT) e
  
        rootPathT = absPathT >>^ snocPathToPath
-}
           
opt :: Expr -> Expr
opt expr = {- trace ("(depth, count) "++ show (depth expr)) $ -} debugOpt expr optimizedExpr

  where
    -- optimizedExpr = applyExpr (strategy >>> projectT) expr
    -- optimizedExpr = applyExpr (test >>> projectT) expr
    optimizedExpr = applyExpr (optimizeR >>> projectT) expr
