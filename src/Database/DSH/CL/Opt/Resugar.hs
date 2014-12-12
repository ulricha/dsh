{-# LANGUAGE PatternSynonyms #-}

-- | Resguaring rules that restore a source comprehension form from
-- the desugared 'concatMap' form.
module Database.DSH.CL.Opt.Resugar
    ( resugarR
    ) where

import           Control.Arrow

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import           Database.DSH.CL.Opt.PartialEval

pattern ConcatP xs   <- AppE1 _ Concat xs
pattern SingletonP x <- AppE1 _ Singleton x
pattern GuardP p     <- AppE1 _ Guard p

-- | Eliminate a singleton list in a comprehension head.
-- concat [ [e] | qs ] => [ e | qs ]
concatCompSingletonR :: RewriteC CL
concatCompSingletonR = do
    ConcatP (Comp (ListT ty) (SingletonP e) qs) <- promoteT idR
    return $ inject $ Comp ty e qs

-- | Eliminate a singleton literal list in a comprehension head.
-- concat [ [v] | qs ] => [ v | qs ]
concatCompSingletonLitR :: RewriteC CL
concatCompSingletonLitR = do
    ConcatP (Comp _ (Lit (ListT ty) (ListV [v])) qs) <- promoteT idR
    return $ inject $ Comp (ListT $ ListT ty) (Lit ty v) qs

-- | Merge nested comprehensions
-- concat [ [ e | qs' ] | qs ] => [ e | qs, qs' ]
concatNestedCompR :: RewriteC CL
concatNestedCompR = do
    ConcatP (Comp _ (Comp compTy innerHead innerQs) outerQs) <- promoteT idR
    return $ inject $ Comp compTy innerHead (appendNL outerQs innerQs)

-- | Eliminate the guard combinator
-- [ e | qs, x <- guard p, qs' ] => [ e | qs, p, qs' ]
-- FIXME To be extra sure, we should check wether x occurs free in  or qs'
guardGeneratorR :: RewriteC (NL Qual)
guardGeneratorR = readerT $ \qual -> case qual of
    BindQ _ (GuardP p) :* qs -> do
        return $ GuardQ p :* qs
    S (BindQ _ (GuardP p))     -> do
        return $ S $ GuardQ p
    _                          -> fail "not a guard combinator"

guardGeneratorsR :: RewriteC CL
guardGeneratorsR = do
    Comp _ _ _ <- promoteT idR
    childR CompQuals (promoteR $ onetdR guardGeneratorR)

resugarRulesR :: RewriteC CL
resugarRulesR = readerT $ \expr -> case expr of
    ExprCL (ConcatP (Comp _ _ _)) -> concatCompSingletonR
                                     <+ concatCompSingletonLitR
                                     <+ concatNestedCompR
    ExprCL (Comp _ _ _)           -> guardGeneratorsR
    ExprCL _                      -> partialEvalR
    _                    -> fail "no resugaring rule applies"

-- | Resugar a comprehension.
resugarR :: RewriteC CL
resugarR = (repeatR $ anybuR resugarRulesR) >>> debugShow "resugared"
