module Language.ParallelLang.Translate.RewritePhases(runRWPhase1, runRWPhase2) where

import Language.ParallelLang.FKL.Primitives

import Language.ParallelLang.Common.Data.Config
import Language.ParallelLang.Translate.TransM
import Language.ParallelLang.Translate.Rewriter

import Control.Applicative hiding (Const, optional)

runRWPhase1 :: TExpr -> TransM TExpr
runRWPhase1 e = rewriteAST rwPhase1 e >>= rewriteAST rwPhase1'

runRWPhase2 :: TExpr -> TransM TExpr
runRWPhase2 = rewriteAST rwPhase2

rwPhase2 :: RewriteRule
rwPhase2 x = (pure x) 

rwPhase1' :: RewriteRule
rwPhase1' = optional (withOpt PermuteOpt) rewriteIndexDist

rwPhase1 :: RewriteRule
rwPhase1 x = (pure x) 
              

rewriteIndexDist :: RewriteRule
rewriteIndexDist e = return e