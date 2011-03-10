module Language.ParallelLang.Translate.VariableUsage(optimiseVarUsage) where
    
import Language.ParallelLang.FKL.Data.FKL

import qualified Data.Map as M

optimiseVarUsage :: Expr -> Expr
optimiseVarUsage = fst . flip countUses M.empty

type VarUses = M.Map String Int

vAdd :: VarUses -> VarUses -> VarUses
vAdd = M.unionWith (+)

countUses :: Expr -> M.Map String Expr -> (Expr, VarUses)
countUses (App t e1 es) ms = let (e1', u) = countUses e1 ms
                                 (es', us) = unzip $ map (flip countUses ms) es
                              in (App t e1' es', foldr1 vAdd (u:us))
countUses (Fn t n l args e) ms = let (e', u) = countUses e (foldr M.delete ms args)
                                  in (Fn t n l args e', (foldr M.delete u args))
countUses (Let t n e1 e2) ms = let (e1', u1) = countUses e1 ms
                                   (e2', u2) = case M.lookup n u2 of
                                                (Just 1) -> countUses e2 $ M.insert n e1' ms
                                                _        -> countUses e2 ms
                                in case M.lookup n u2 of
                                    Nothing  -> (e2', u2)
                                    (Just 0) -> (e2', u2)
                                    (Just 1) -> (e2', vAdd u1 u2)
                                    (Just _) -> (Let t n e1' e2', vAdd u1 $ M.delete n u2)
countUses v@(Var _ n 0) ms = let use = M.singleton n 1
                                 res = case M.lookup n ms of
                                        Just e -> e
                                        Nothing -> v
                              in (res, use) 
countUses v@(Var _ _ _) ms = (v, M.empty)
countUses (If t e1 e2 e3) ms = let (e1', u1) = countUses e1 ms
                                   (e2', u2) = countUses e2 ms
                                   (e3', u3) = countUses e3 ms
                                in (If t e1' e2' e3', vAdd u1 $ vAdd u2 u3)
countUses (BinOp t o e1 e2) ms = let (e1', u1) = countUses e1 ms
                                     (e2', u2) = countUses e2 ms
                                  in (BinOp t o e1' e2', vAdd u1 u2)
countUses c@(Const _ _) _ = (c, M.empty)
countUses n@(Nil _) _     = (n, M.empty)
countUses (Proj t l e i) ms = let (e', u) = countUses e ms
                               in (Proj t l e' i, u)