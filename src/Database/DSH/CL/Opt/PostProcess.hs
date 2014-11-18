module Database.DSH.CL.Opt.PostProcess
    ( introduceCartProductsR
    , mergeGuardsR
    , introduceRestrictsR
    , identityCompR
    , guardpushbackR
    ) where

import           Control.Applicative
import           Control.Arrow
import qualified Data.Set                   as S

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Aux
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.Common.Lang

--------------------------------------------------------------------------------
-- Cleaning up

-- FIXME partial evaluation could be useful as well to eliminate tuple
-- construction

identityCompR :: RewriteC CL
identityCompR = do
    Comp _ (Var _ x) (S (BindQ x' xs)) <- promoteT idR
    guardM $ x == x'
    return $ inject xs

--------------------------------------------------------------------------------
-- 

qualsguardpushbackR :: RewriteC (NL Qual)
qualsguardpushbackR = innermostR $ readerT $ \quals -> case quals of
    GuardQ p :* BindQ x xs :* qs -> return $ BindQ x xs :* GuardQ p :* qs
    GuardQ p :* (S (BindQ x xs)) -> return $ BindQ x xs :* (S (GuardQ p))
    _                            -> fail "no pushable guard"
                    

guardpushbackR :: RewriteC CL
guardpushbackR = do
    Comp t h _ <- promoteT idR
    qs' <- childT CompQuals (promoteR qualsguardpushbackR) >>> projectT
    return $ inject $ Comp t h qs'

--------------------------------------------------------------------------------
-- Turn adjacent generators into cartesian products:
-- [ e | ..., x <- xs, y <- ys, qs ]
-- =>
-- [ e[x/fst x][y/snd x] | ..., x <- xs × ys, qs[x/fst x][y/snd x] ]

mkproduct :: (Ident, Expr) -> (Ident, Expr) -> (RewriteC CL, Qual)
mkproduct (x, xs) (y, ys) =
    -- Conditions for the rewrite are fulfilled.
    let xst          = typeOf xs
        yst          = typeOf ys
        xt           = elemT xst
        yt           = elemT yst
        tuplifyHeadR = tuplifyR x (x, xt) (y, yt)
        joinGen      = BindQ x (P.cartproduct xs ys)

    in (tuplifyHeadR, joinGen)

cartProductR :: Rewrite CompCtx TuplifyM (NL Qual)
cartProductR = do
    readerT $ \e -> case e of
        BindQ x xs :* BindQ y ys :* qs -> do
            -- xs and ys generators must be independent
            guardM $ x `notElem` freeVars ys

            let (tuplifyHeadR, q') = mkproduct (x, xs) (y, ys)
            -- Next, we apply the tuplifyHeadR rewrite to the tail,
            -- i.e. to all following qualifiers
            -- FIXME why is extractT required here?
            qs' <- catchesT [ liftstateT $ (constT $ return qs)
                                           >>> (extractR tuplifyHeadR)
                            , constT $ return qs
                            ]

            -- The tuplify rewrite must be handed to the top level
            constT $ put tuplifyHeadR

            return $ q' :* qs'

        BindQ x xs :* (S (BindQ y ys)) -> do
            -- xs and ys generators must be independent
            guardM $ x `notElem` freeVars ys

            let (tuplifyHeadR, q') = mkproduct (x, xs) (y, ys)

            -- The tuplify rewrite must be handed to the top level
            constT $ put tuplifyHeadR

            return (S q')
        _ -> fail "no match"


introduceCartProductsR :: RewriteC CL
introduceCartProductsR = do
    Comp t _ _          <- promoteT idR
    (tuplifyHeadR, qs') <- statefulT idR $ childT CompQuals (promoteR cartProductR) >>> projectT
    ExprCL h'           <- childT CompHead tuplifyHeadR
    return $ inject $ Comp t h' qs'

--------------------------------------------------------------------------------
-- Turn comprehension guards into restrict combinators
--
-- [ e | ..., x <- xs, p x, ... ]
-- =>
-- [ e | ..., x <- restrict xs [ p x | x <- xs ], ... ]

restrictQualR :: RewriteC (NL Qual)
restrictQualR = do
    readerT $ \e -> case e of
        BindQ x xs :* GuardQ p :* qs -> do
            [x'] <- return $ freeVars p
            guardM $ x == x'
            -- FIXME use let-binding
            let xs' = P.restrict xs (P.singleGenComp p x xs)
            return $ inject $ BindQ x xs' :* qs
        BindQ x xs :* (S (GuardQ p)) -> do
            [x'] <- return $ freeVars p
            guardM $ x == x'
            -- FIXME use let-binding
            let xs' = P.restrict xs (P.singleGenComp p x xs)
            return $ inject $ S $ BindQ x xs'
        _ -> fail "no match"

restrictR :: RewriteC CL
restrictR = do
    Comp _ _ _ <- promoteT idR
    childR CompQuals (promoteR $ restrictQualR)

restrictWorkerT :: MergeGuard
restrictWorkerT comp guard guardsToTry leftOverGuards = do
    let C ty h qs = comp
    env <- S.fromList <$> inScopeNames <$> contextT
    let compExpr = ExprCL $ Comp ty h (insertGuard guard env qs)
    ExprCL (Comp _ _ qs') <- constT (return compExpr) >>> restrictR
    return (C ty h qs', guardsToTry, leftOverGuards)

mergeGuardsR :: RewriteC CL
mergeGuardsR = readerT $ \quals -> case quals of
    QualsCL (GuardQ p1 :* S (GuardQ p2))   -> 
        return $ QualsCL $ S $ GuardQ $ p1 `P.conj` p2
    QualsCL (GuardQ p1 :* GuardQ p2 :* qs) -> 
        return $ QualsCL $ GuardQ (p1 `P.conj` p2) :* qs
    _ -> fail "no match"

-- |
introduceRestrictsR :: RewriteC CL
introduceRestrictsR = mergeGuardsIterR restrictWorkerT
