{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Introduce simple theta joins.
module Database.DSH.CL.Opt.ThetaJoin
    ( thetajoinR
    ) where

import           Control.Arrow
import qualified Data.Set                      as S

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary
import qualified Database.DSH.CL.Primitives    as P
import           Database.DSH.Common.Lang

--------------------------------------------------------------------------------
-- Introduce simple theta joins

tuplifyCont :: S.Set Ident -> (Ident, Expr) -> (Ident, Expr) -> NL Qual -> (NL Qual, Expr -> Expr)
tuplifyCont scopeNames (x, xs) (y, ys) qs =
    tuplifyCompContE scopeNames x (x, xt) (y, yt) qs
  where
    xt = elemT $ typeOf xs
    yt = elemT $ typeOf ys

tuplify :: S.Set Ident -> (Ident, Expr) -> (Ident, Expr) -> Expr -> Expr
tuplify scopeNames (x, xs) (y, ys) =
    tuplifyE scopeNames x (x, xt) (y, yt)
  where
    xt = elemT $ typeOf xs
    yt = elemT $ typeOf ys

thetajoinQualsT :: TransformC CL (NL Qual, Expr -> Expr)
thetajoinQualsT =
    readerT $ \e -> case e of
        QualsCL (BindQ x xs :* BindQ y ys :* GuardQ p :* qs) -> do
            guardM $ x /= y
            -- xs and ys generators must be independent
            guardM $ x `notElem` freeVars ys

            -- The predicate must be a join predicate
            joinConjunct <- constT (return p) >>> (splitJoinPredT x y)

            scopeNames <- inScopeNamesT
            let joinGen          = BindQ x (P.thetajoin xs ys (singlePred joinConjunct))
                (qs', substCont) = tuplifyCont scopeNames (x, xs) (y, ys) qs
            return (joinGen :* qs', substCont)

        QualsCL (BindQ x xs :* BindQ y ys :* S (GuardQ p)) -> do
            guardM $ x /= y
            -- xs and ys generators must be independent
            guardM $ x `notElem` freeVars ys

            -- The predicate must be a join predicate
            joinConjunct <- constT (return p) >>> (splitJoinPredT x y)

            scopeNames <- inScopeNamesT
            let joinGen   = BindQ x (P.thetajoin xs ys (singlePred joinConjunct))
                substCont = tuplify scopeNames (x, xs) (y, ys)
            return (S joinGen, substCont)
        QualsCL (q :* _) -> do
            (qs', substCont) <- childT QualsTail thetajoinQualsT
            pure (q :* qs', substCont)
        _ -> fail "no match"

thetajoinR :: [Expr] -> [Expr] -> TransformC CL (CL, [Expr], [Expr])
thetajoinR currentGuards testedGuards = do
    Comp t h _       <- promoteT idR
    (qs', substCont) <- childT CompQuals thetajoinQualsT
    pure ( inject $ Comp t (substCont h) qs'
         , map substCont currentGuards
         , map substCont testedGuards
         )
