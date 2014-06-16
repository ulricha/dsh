module Database.DSH.CL.Opt.AntiJoin
    ( antijoinR
    ) where

import           Control.Arrow

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Aux
import qualified Database.DSH.CL.Primitives    as P
import           Database.DSH.Common.Lang

--------------------------------------------------------------------------------
-- Introduce anti joins (universal quantification)

--------------------------------------------------------------------------------
-- Basic antijoin pattern

-- | Construct an antijoin qualifier given a predicate and two generators. Note
-- that the splitJoinPred call implicitly checks that only x and y occur free in
-- the predicate and no further correlation takes place.
mkantijoinT :: Expr -> Ident -> Ident -> Expr -> Expr -> TransformC (NL Qual) Qual
mkantijoinT joinPred x y xs ys = do
    joinConjunct <- constT (return joinPred) >>> splitJoinPredT x y

    let xst = typeOf xs
        yst = typeOf ys
        jt  = xst .-> yst .-> xst

    -- => [ ... | ..., x <- xs antijoin(p1, p2) ys, ... ]
    return $ BindQ x (AppE2 xst (Prim2 (AntiJoin $ singlePred joinConjunct) jt) xs ys)

-- | Match the basic antijoin pattern in the middle of a qualifier list. This is
-- essentially the operator definition, generalized to multiple qualifiers and
-- an arbitrary comprehension head:
-- [ f x | qs, x <- xs, and [ not (q y) | y <- ys ], qs' ]
-- => [ f x | qs, x <- xs antijoin(q) ys, qs' ]
basicAntiJoinR :: RewriteC (NL Qual)
basicAntiJoinR = do
    -- [ ... | ..., x <- xs, and [ not p | y <- ys ], ... ]
    BindQ x xs :* GuardQ (AppE1 _ (Prim1 And _)
                                  (Comp _ (UnOp _ (SUBoolOp Not) p)
                                          (S (BindQ y ys))))  :* qs <- idR
    q' <- mkantijoinT p x y xs ys
    return $ q' :* qs

-- | Match a NOT IN antijoin pattern at the end of a list
basicAntiJoinEndR :: RewriteC (NL Qual)
basicAntiJoinEndR = do
    -- [ ... | ..., x <- xs, and [ True | y <- ys, not p ] ]
    BindQ x xs :* S (GuardQ (AppE1 _ (Prim1 And _)
                                     (Comp _ (UnOp _ (SUBoolOp Not) p)
                                             (S (BindQ y ys))))) <- idR
    q' <- mkantijoinT p x y xs ys
    return (S q')

--------------------------------------------------------------------------------
-- Doubly Negated existential quantifier (NOT EXISTS)

notinR :: RewriteC (NL Qual)
notinR = do
    BindQ x xs :*
        (GuardQ (UnOp _ (SUBoolOp Not)
                         (AppE1 _ (Prim1 Or _)
                                  (Comp _ q (BindQ y ys :* (S (GuardQ p))))))) :* qs <- idR

    --

    q' <- mkClass15AntiJoinT x xs y ys p q
    return $ q' :* qs

notinEndR :: RewriteC (NL Qual)
notinEndR = do
    BindQ x xs :*
        (S (GuardQ (UnOp _ (SUBoolOp Not)
                            (AppE1 _ (Prim1 Or _)
                                     (Comp _ q (BindQ y ys :* (S (GuardQ p)))))))) <- idR

    --

    q' <- mkClass15AntiJoinT x xs y ys p q
    return (S q')

--------------------------------------------------------------------------------
-- Universal quantification with range predicates

-- | Turn universal quantification with range and quantifier predicates into an
-- antijoin. We use the classification of queries in Claussen et al.: Optimizing
-- Queries with Universal Quantification in Object-Oriented and
-- Object-Relational Databases (VLDB 1995).
universalR :: RewriteC (NL Qual)
universalR = do
    -- [ ... | ..., x <- xs, and [ q y | y <- ys, p x y ], ... ]
    BindQ x xs :* (GuardQ (AppE1 _ (Prim1 And _)
                                   (Comp _ q ((BindQ y ys) :* (S (GuardQ p)))))) :* qs <- idR

    q' <- mkClass15AntiJoinT x xs y ys p q
    return $ q' :* qs

universalEndR :: RewriteC (NL Qual)
universalEndR = do
    -- [ ... | ..., x <- xs, and [ q y | y <- ys, p x y ] ]
    BindQ x xs :* (S (GuardQ (AppE1 _ (Prim1 And _)
                                      (Comp _ q ((BindQ y ys) :* (S (GuardQ p))))))) <- idR

    q' <- mkClass15AntiJoinT x xs y ys p q
    return (S q')

-- This rewrite implements plan 14 for Query Class 15 in Claussen et al.,
-- Optimizing Queries with Universal Quantification... (VLDB, 1995).  Class 15
-- contains queries in which the range predicate ranges over both relations,
-- i.e. x and y occur free. The quantifier predicate on the other hand ranges
-- only over the inner relation.
mkClass15AntiJoinT :: Ident -> Expr -> Ident -> Expr -> Expr -> Expr -> TransformC (NL Qual) Qual
mkClass15AntiJoinT x xs y ys p q = do
    -- Check that the quantifier predicate only ranges over the inner relation
    guardM $ freeVars q == [y]

    -- The range predicate must have the form of a join predicate. This
    -- implicitly checks that the range predicate ranges over x and y.
    joinConjunct <- constT (return p) >>> splitJoinPredT x y

    let yst = typeOf ys
        yt  = elemT yst

    -- => [ ... | ..., x <- xs antijoin(p1, p2) [ y | y <- ys, not q ], ...]
    let ys' = Comp yst (Var yt y) (BindQ y ys :* (S (GuardQ (P.scalarUnOp (SUBoolOp Not) q))))
        q'  = BindQ x (P.antijoin xs ys' (singlePred joinConjunct))
    return q'

universalQualsR :: RewriteC (NL Qual)
universalQualsR = onetdR $ basicAntiJoinR
                           <+ basicAntiJoinEndR
                           <+ notinR
                           <+ notinEndR
                           <+ universalR
                           <+ universalEndR

antijoinR :: RewriteC CL
antijoinR = do
    Comp _ _ _ <- promoteT idR
    childR CompQuals (promoteR universalQualsR)
