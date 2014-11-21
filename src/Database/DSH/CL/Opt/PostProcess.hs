module Database.DSH.CL.Opt.PostProcess
    ( introduceCartProductsR
    , guardpushbackR
    ) where

import           Control.Arrow

import           Database.DSH.Common.Lang
import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Aux
import qualified Database.DSH.CL.Primitives as P

--------------------------------------------------------------------------------

qualsguardpushbackR :: RewriteC (NL Qual)
qualsguardpushbackR = innermostR $ readerT $ \quals -> case quals of
    GuardQ p :* BindQ x xs :* qs -> return $ BindQ x xs :* GuardQ p :* qs
    GuardQ p :* (S (BindQ x xs)) -> return $ BindQ x xs :* (S (GuardQ p))
    _                            -> fail "no pushable guard"
                    

-- | Push all guards to the end of the qualifier list to bring
-- generators closer together.
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
