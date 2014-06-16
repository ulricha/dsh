{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Introduce simple theta joins.
module Database.DSH.CL.Opt.ThetaJoin
    ( thetajoinR
    ) where

import           Control.Arrow

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Aux
import           Database.DSH.Common.Lang

--------------------------------------------------------------------------------
-- Introduce simple theta joins

-- | Concstruct an thetajoin generator
mkthetajoinT
  :: Expr  -- ^ The predicate
  -> Ident -- ^ Identifier from the first generator
  -> Ident -- ^ Identifier from the second generator
  -> Expr  -- ^ First generator expression
  -> Expr  -- ^ Second generator expression
  -> Transform CompCtx TuplifyM (NL Qual) (RewriteC CL, Qual)
mkthetajoinT joinPred x y xs ys = do
    -- The predicate must be a join predicate
    joinConjunct <- constT (return joinPred) >>> (liftstateT $ splitJoinPredT x y)

    -- Conditions for the rewrite are fulfilled.
    let xst          = typeOf xs
        yst          = typeOf ys
        xt           = elemT xst
        yt           = elemT yst
        pt           = listT $ pairT xt yt
        jt           = xst .-> (yst .-> pt)
        tuplifyHeadR = tuplifyR x (x, xt) (y, yt)
        joinGen      = BindQ x
                         (AppE2 pt
                           (Prim2 (ThetaJoin (singlePred joinConjunct)) jt)
                           xs ys)

    return (tuplifyHeadR, joinGen)

-- | Match a thetajoin pattern in the middle of a qualifier list
thetajoinQualR :: Rewrite CompCtx TuplifyM (NL Qual)
thetajoinQualR = do
    -- We need two generators followed by a predicate
    BindQ x xs :* BindQ y ys :* GuardQ p :* qs <- promoteT idR

    (tuplifyHeadR, q') <- mkthetajoinT p x y xs ys

    -- Next, we apply the tuplifyHeadR rewrite to the tail, i.e. to all following
    -- qualifiers
    -- FIXME why is extractT required here?
    qs' <- catchesT [ liftstateT $ (constT $ return qs) >>> (extractR tuplifyHeadR)
                    , constT $ return qs
                    ]

    -- The tuplify rewrite must be handed to the top level
    constT $ put tuplifyHeadR

    return $ q' :* qs'

-- | Match a thetajoin pattern at the end of a qualifier list
thetajoinQualEndR :: Rewrite CompCtx TuplifyM (NL Qual)
thetajoinQualEndR = do
    -- We need two generators followed by a predicate
    BindQ x xs :* BindQ y ys :* (S (GuardQ p)) <- promoteT idR

    (tuplifyHeadR, q') <- mkthetajoinT p x y xs ys

    -- The tuplify rewrite must be handed to the top level
    constT $ put tuplifyHeadR

    return (S q')

thetajoinQualsR :: Rewrite CompCtx TuplifyM (NL Qual)
thetajoinQualsR = onetdR (thetajoinQualEndR <+ thetajoinQualR)

thetajoinR :: [Expr] -> [Expr] -> TransformC CL (CL, [Expr], [Expr])
thetajoinR currentGuards testedGuards = do
    Comp t _ _          <- promoteT idR
    (tuplifyHeadR, qs') <- statefulT idR $ childT CompQuals (promoteR thetajoinQualsR >>> projectT)
    e'                  <- (tryR $ childT CompHead tuplifyHeadR) >>> projectT
    -- FIXME should propably wrap tuplifyHeadR in tryR
    currentGuards'      <- constT (return currentGuards) >>> mapT (extractR tuplifyHeadR)
    testedGuards'       <- constT (return testedGuards) >>> mapT (extractR tuplifyHeadR)
    return $ (inject $ Comp t e' qs', currentGuards', testedGuards')
