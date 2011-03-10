module Language.ParallelLang.Translate.Rewriter (rewriteAST, RewriteRule, optional) where
    
import Language.ParallelLang.FKL.Data.FKL

import Language.ParallelLang.Translate.TransM

import Control.Applicative hiding (Const, optional)

type RewriteRule = Expr -> TransM Expr

optional :: TransM Bool -> RewriteRule -> RewriteRule
optional b r e = do
                b' <- b
                case b' of
                 False -> return e
                 True  -> r e
                 
rewriteAST :: RewriteRule -> ([Expr], Expr) -> TransM ([Expr], Expr)
rewriteAST r (es, e) = do
                             rs' <- mapM (rewriteTree r) es
                             r' <- rewriteTree r e
                             return (rs', r')



rewriteTree :: RewriteRule -> RewriteRule
rewriteTree r e = recurse e
  where
    recurse :: Expr -> TransM Expr
    recurse ex = do
                   ex' <- r ex
                   rewriteAST' ex'
    rewriteAST' :: Expr -> TransM Expr
    rewriteAST' (App  t ex1 exs) = (App t) <$> recurse ex1 <*> mapM recurse exs
    rewriteAST' (Fn t n i as ex) = (Fn t n i as) <$> recurse ex
    rewriteAST' (Let t s ex1 ex2) = (Let t s) <$> recurse ex1 <*> recurse ex2
    rewriteAST' (If t ex1 ex2 ex3) = (If t) <$> recurse ex1 <*> recurse ex2 <*> recurse ex3
    rewriteAST' (BinOp t o ex1 ex2) = (BinOp t o) <$> recurse ex1 <*> recurse ex2
    rewriteAST' c@(Const _ _) = pure c
    rewriteAST' v@(Var _ _ _) = pure v
    rewriteAST' n@(Nil _) = pure n
    rewriteAST' (Proj t l ex i) = (flip (Proj t l) i) <$> recurse ex 
