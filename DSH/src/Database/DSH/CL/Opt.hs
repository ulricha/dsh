{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | This module performs optimizations on the Comprehension Language (CL).
module Database.DSH.CL.Opt 
  ( opt ) where
       
import           Control.Arrow

import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure

import           Database.DSH.CL.Opt.Aux
import           Database.DSH.CL.Opt.Support
import           Database.DSH.CL.Opt.Normalize
import           Database.DSH.CL.Opt.CompNormalization
import           Database.DSH.CL.Opt.FlatJoin
import           Database.DSH.CL.Opt.NestJoin
import           Database.DSH.CL.Opt.Operators

--------------------------------------------------------------------------------
-- Rewrite Strategy: Rule Groups

-- Clean up remains and perform partial evaluation on the current node
cleanupR :: RewriteC CL
cleanupR = anybuR $ extractR houseCleaningR
                    <+ extractR partialEvalR

flatJoins :: RewriteC CL
flatJoins = (promoteR (tryR pushSemiFilters) >>> semijoinR)
            <+ (promoteR (tryR pushAntiFilters) >>> antijoinR)
            <+ (promoteR (tryR pushEquiFilters) >>> eqjoinR)
            
-- FIXME add m_norm_1R once tables for benchmark queries exist
-- | Comprehension normalization rules 1 to 3.
compNormEarly :: RewriteC CL
compNormEarly = m_norm_2R <+ m_norm_3R

-- | Comprehension normalization rules 4 and 5. Beware: these rewrites should
-- propably occur late in the chain, as they might prohibit semijoin/antijoin
-- introduction
compNormLate :: RewriteC CL
compNormLate = m_norm_4R <+ m_norm_5R
           
nestJoins :: RewriteC CL
nestJoins = (nestjoinHeadR >>> cleanupNestJoinR)
            <+ nestjoinGuardR
            
  where
    cleanupNestJoinR :: RewriteC CL
    cleanupNestJoinR = repeatR $ anytdR combineNestJoinsR

--------------------------------------------------------------------------------
-- Rewrite Strategy
            
optimizeR :: RewriteC CL
optimizeR = tryR normalizeR >>> repeatR (optCompR <+ optNonCompR)
  where
    optCompR :: RewriteC CL
    optCompR = do
        c@(Comp _ _ _) <- promoteT idR
        debugUnit "optCompR at" c

        repeatR $ do
            e <- promoteT idR
            debugUnit "comp at" (e :: Expr)
            extractR cleanupR
              <+ compNormEarly
              <+ (promoteR (tryR pushSimpleFilters) >>> selectR isSimplePred)
              <+ flatJoins
              <+ anyR optimizeR
              <+ nestJoins
              <+ extractR cleanupR

    -- For non-comprehension nodes, simply descend
    optNonCompR :: RewriteC CL
    optNonCompR = do
        e <- idR
        -- debugUnit "noncomp at" (e :: CL)
        anyR optimizeR

           
opt :: Expr -> Expr
opt expr = debugOpt expr optimizedExpr

  where
    -- optimizedExpr = applyExpr (strategy >>> projectT) expr
    -- optimizedExpr = applyExpr (test >>> projectT) expr
    optimizedExpr = applyExpr (optimizeR >>> projectT) expr
