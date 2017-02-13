module Database.DSH.CL.Opt.PostProcess
    ( introduceCartProductsR
    ) where

import qualified Data.Set                      as S

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary
import qualified Database.DSH.CL.Primitives    as P
import           Database.DSH.Common.Kure
import           Database.DSH.Common.Lang

--------------------------------------------------------------------------------
-- Turn adjacent generators into cartesian products:
-- [ e | ..., x <- xs, y <- ys, qs ]
-- =>
-- [ e[x/fst x][y/snd x] | ..., x <- xs × ys, qs[x/fst x][y/snd x] ]

tuplifyQualsHead :: S.Set Ident -> (Ident, Expr) -> (Ident, Expr) -> NL Qual -> Expr -> (NL Qual, Expr)
tuplifyQualsHead scopeNames (x, xs) (y, ys) =
    let xst          = typeOf xs
        yst          = typeOf ys
        xt           = elemT xst
        yt           = elemT yst
    in tuplifyCompE scopeNames x (x, xt) (y, yt)

tuplifyHead :: S.Set Ident -> (Ident, Expr) -> (Ident, Expr) -> Expr -> Expr
tuplifyHead scopeNames (x, xs) (y, ys) =
    let xst          = typeOf xs
        yst          = typeOf ys
        xt           = elemT xst
        yt           = elemT yst
    in tuplifyE scopeNames x (x, xt) (y, yt)

cartProductQualsT :: Expr -> TransformC CL (NL Qual, Expr)
cartProductQualsT headExp =
    readerT $ \e -> case e of
        QualsCL (BindQ x xs :* BindQ y ys :* qs) -> do
            -- xs and ys generators must be independent
            guardM $ x `notElem` freeVars ys

            scopeNames <- inScopeNamesT
            let prodGen         = BindQ x (P.cartproduct xs ys)
                (qs', headExp') = tuplifyQualsHead scopeNames (x, xs) (y, ys) qs headExp
            return (prodGen :* qs', headExp')

        QualsCL (BindQ x xs :* S (BindQ y ys)) -> do
            -- xs and ys generators must be independent
            guardM $ x `notElem` freeVars ys

            scopeNames <- inScopeNamesT
            let prodGen  = BindQ x (P.cartproduct xs ys)
                headExp' = tuplifyHead scopeNames (x, xs) (y, ys) headExp
            return (S prodGen, headExp')
        QualsCL (q :* _) -> do
            (qs', headExp') <- childT QualsTail (cartProductQualsT headExp)
            pure (q :* qs', headExp')
        _ -> fail "no match"

introduceCartProductsR :: RewriteC CL
introduceCartProductsR = logR "postprocess.cartproduct" $ do
    Comp t h _ <- promoteT idR
    (qs', h')  <- childT CompQuals (cartProductQualsT h)
    return $ inject $ Comp t h' qs'
