module Language.ParallelLang.Translate.RewritePhases(runRWPhase1, runRWPhase2) where

import Language.ParallelLang.FKL.Data.FKL
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
rwPhase1 x = (pure x) {- >>=
              optional (withOpt LetSimple) removeLetVarIsSimple >>=
              -- rewriteCombineLift >>=
              -- rewriteRestrictLift >>=
              -- rewriteIndexPromote >>=
              -- rewritePromote >>=
              -- rewriteHigherLiftedOp >>=
              -- removeHigherLifted >>=
              optional (withOpt LetSimple) removeLetVarIsSimple  -}

              

{-
Rules
-}

{-
removeLetVarIsSimple :: RewriteRule
removeLetVarIsSimple l@(Let _ v e1 e2) = return $ case isSimpleExpr e1 of
                                                    False -> l
                                                    True -> substitute v e1 e2
removeLetVarIsSimple e1 = return e1
-}
{-
removeHigherLifted :: RewriteRule
removeHigherLifted a@(App rt (Var _ n d) es) | d > 1 =
                        do
                            let rt' = unliftTypeN (d - 1) rt
                            fv1 <- getFreshVar
                            let v1 = Var (typeOf $ head es) fv1 0
                            let es' = [extractF e' (intF (d - 1)) | e' <- v1 : (tail es) ]
                            let ets' = map typeOf es'
                            return $ letF fv1 (head es)
                                     $ insertF   
                                        (App rt' (Var (foldr (.->) rt' ets') n 1) es')
                                        v1 (intF $ d - 1)
                                            | otherwise = return a
removeHigherLifted e = return e
-}
{-
rewriteHigherLiftedOp :: RewriteRule
rewriteHigherLiftedOp a@(BinOp rt (Op n d) e1 e2) | d > 1 =
                    do
                        fv1 <- getFreshVar
                        let v1 = Var (typeOf e1) fv1 0
                        let e1' = extractF v1 $ intF $ d - 1
                        let e2' = extractF e2 $ intF $ d - 1
                        let rt' = unliftTypeN (d - 1) rt
                        return $ letF fv1 e1 
                                    $ insertF (BinOp rt' (Op n 1) e1' e2') v1 (intF $ d - 1)
                                                 | otherwise = return a
rewriteHigherLiftedOp e = return e
-}
{-
rewritePromote :: RewriteRule
rewritePromote (App _ (Var _ "promote" 0) [e1, e2]) = 
                            let d = listDepth $ typeOf e2
                             in if d > 1
                                 then do
                                       fv2 <- getFreshVar
                                       let v2 = Var (typeOf e2) fv2 0
                                       return $ letF fv2 e2 $
                                                 insertF (distF e1 (extractF v2 (intF $ d - 1))) 
                                                         v2 (intF $ d - 1) 
                                 else return $ distF e1 e2
rewritePromote e = return e
-}
{-
rewriteRestrictLift :: RewriteRule
rewriteRestrictLift a@(App _ (Var _ "restrict" d) [e1, e2]) | d > 0 =
                            do
                             fv1 <- getFreshVar
                             let v1 = Var (typeOf e1) fv1 0
                             return $ letF fv1 e1 $
                                        insertF (restrictF (extractF v1 (intF d)) (extractF e2 (intF d))) 
                                                v1 (intF d)
                                                            | otherwise = return a
rewriteRestrictLift e = return e
-}
{-
rewriteCombineLift :: RewriteRule
rewriteCombineLift a@(App _ (Var _ "combine" d) [e1, e2, e3]) | d > 0 = 
                              do
                                fv1 <- getFreshVar
                                fv2 <- getFreshVar
                                fv3 <- getFreshVar
                                let v1 = Var (typeOf e1) fv1 0
                                let v2 = Var (typeOf e2) fv2 0
                                let v3 = Var (typeOf e3) fv3 0
                                return $ letF fv1 e1 $ 
                                          letF fv2 e2 $
                                           letF fv3 e3 $ insertF (combineF (extractF v1 (intF d)) 
                                                                          (extractF v2 (intF d)) 
                                                                          (extractF v3 (intF d))) 
                                                                v1 (intF d) 
                                                              | otherwise = return a
rewriteCombineLift e = return e
-}
rewriteIndexDist :: RewriteRule
{-
rewriteIndexDist a@(CloLApp _ (Var _ "index") [(CloApp _ (Var _ "dist") [e1, e2]), e3]) | e2 == e3 = return $ bPermuteF e1 e3
                                                                                        | otherwise = return a -}
rewriteIndexDist e = return e

{-
rewriteIndexPromote :: RewriteRule
rewriteIndexPromote a@(App _ (Var _ "index" d) [(App _ (Var _ "promote" 0) [e1, e2]), e3]) | d > 1 && e2 == e3 =
                                do  
                                    fv <- getFreshVar
                                    let v = Var (typeOf e2) fv 0
                                    return $ letF fv e2 $ insertF (bPermuteF e1 (extractF v (intF $ d - 1))) v (intF $ d - 1)
                                                                                           | otherwise = return a
rewriteIndexPromote e = return e    
-}