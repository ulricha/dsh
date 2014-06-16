module Database.DSH.CL.Opt.SemiJoin
    ( semijoinR
    ) where

import           Control.Arrow

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Aux
import           Database.DSH.Common.Lang

--------------------------------------------------------------------------------
-- Introduce semi joins (existential quantification)

-- | Construct a semijoin qualifier given a predicate and two generators
-- Note that the splitJoinPred call implicitly checks that only x and y
-- occur free in the predicate and no further correlation takes place.
mksemijoinT :: Expr -> Ident -> Ident -> Expr -> Expr -> TransformC (NL Qual) Qual
mksemijoinT joinPred x y xs ys = do
    joinConjunct <- constT (return joinPred) >>> splitJoinPredT x y

    let xst = typeOf xs
        yst = typeOf ys
        jt  = xst .-> yst .-> xst

    -- => [ ... | ..., x <- xs semijoin(p1, p2) ys, ... ]
    return $ BindQ x (AppE2 xst (Prim2 (SemiJoin $ singlePred joinConjunct) jt) xs ys)

-- | Match a IN semijoin pattern in the middle of a qualifier list
elemR :: RewriteC (NL Qual)
elemR = do
    -- [ ... | ..., x <- xs, or [ p | y <- ys ], ... ]
    BindQ x xs :* GuardQ (AppE1 _ (Prim1 Or _) (Comp _ p
                                                       (S (BindQ y ys)))) :* qs <- idR
    q' <- mksemijoinT p x y xs ys
    return $ q' :* qs

-- | Match a IN semijoin pattern at the end of a list
elemEndR :: RewriteC (NL Qual)
elemEndR = do
    -- [ ... | ..., x <- xs, or [ p | y <- ys ] ]
    BindQ x xs :* (S (GuardQ (AppE1 _ (Prim1 Or _) (Comp _ p
                                                           (S (BindQ y ys)))))) <- idR
    q' <- mksemijoinT p x y xs ys
    return (S q')

existentialQualsR :: RewriteC (NL Qual)
existentialQualsR = onetdR (elemR <+ elemEndR)

semijoinR :: RewriteC CL
semijoinR = do
    Comp _ _ _ <- promoteT idR
    childR CompQuals (promoteR existentialQualsR)
