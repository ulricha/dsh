{-# LANGUAGE PatternSynonyms #-}

module Database.DSH.CL.Opt.SemiJoin
    ( semijoinR
    ) where

import           Control.Arrow
import qualified Data.Traversable as T
import           Data.List
import           Data.List.NonEmpty(NonEmpty((:|)))
import qualified Data.List.NonEmpty as NL

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Aux
import           Database.DSH.Common.Lang
import qualified Database.DSH.CL.Primitives as P

--------------------------------------------------------------------------------
-- Introduce semi joins (existential quantification)

pattern POr xs <- AppE1 _ (Prim1 Or _) xs
pattern PTrue = Lit BoolT (BoolV True)

existentialQualR :: RewriteC (NL Qual)
existentialQualR = readerT $ \quals -> case quals of
    -- Special case: existential quantifier without a quantifier predicate
    -- [ ... | ..., x <- xs, or [ True | y <- ys, ps ], ... ]
    BindQ x xs :* (GuardQ (POr (Comp _ PTrue (BindQ y ys :* ps)))) :* qs -> do
        -- Generators have to be indepedent
        guardM $ x `notElem` freeVars ys

        semijoinGen <- mkExistentialSemiJoinT (x, xs) (y, ys) Nothing (Just ps)
        return $ semijoinGen :* qs

    -- Special case: existential quantifier without a quantifier predicate
    -- [ ... | ..., x <- xs, or [ True | y <- ys, ps ] ]
    BindQ x xs :* (S (GuardQ (POr (Comp _ PTrue (BindQ y ys :* ps))))) -> do
        -- Generators have to be indepedent
        guardM $ x `notElem` freeVars ys

        semijoinGen <- mkExistentialSemiJoinT (x, xs) (y, ys) Nothing (Just ps)
        return $ S semijoinGen

    -- Special case: Existential quantifier without a range predicate
    -- [ ... | ..., x <- xs, or [ q | y <- ys ], ... ]
    BindQ x xs :* (GuardQ (POr (Comp _ q (S (BindQ y ys))))) :* qs -> do
        -- Generators have to be indepedent
        guardM $ x `notElem` freeVars ys

        semijoinGen <- mkExistentialSemiJoinT (x, xs) (y, ys) (Just q) Nothing
        return $ semijoinGen :* qs

    -- Special case: Existential quantifier without a range predicate
    -- [ ... | ..., x <- xs, or [ q | y <- ys ] ]
    BindQ x xs :* (S (GuardQ (POr (Comp _ q (S (BindQ y ys)))))) -> do
        -- Generators have to be indepedent
        guardM $ x `notElem` freeVars ys

        semijoinGen <- mkExistentialSemiJoinT (x, xs) (y, ys) (Just q) Nothing
        return $ S semijoinGen
    
    -- Existential quantifier with range and quantifier predicates
    -- [ ... | ..., x <- xs, or [ True | y <- ys, ps ], ... ]
    BindQ x xs :* (GuardQ (POr (Comp _ q (BindQ y ys :* ps)))) :* qs -> do
        -- Generators have to be indepedent
        guardM $ x `notElem` freeVars ys

        semijoinGen <- mkExistentialSemiJoinT (x, xs) (y, ys) (Just q) (Just ps)
        return $ semijoinGen :* qs

    -- Existential quantifier with range and quantifier predicates
    -- [ ... | ..., x <- xs, or [ True | y <- ys, ps ] ]
    BindQ x xs :* (S (GuardQ (POr (Comp _ q (BindQ y ys :* ps))))) -> do
        -- Generators have to be indepedent
        guardM $ x `notElem` freeVars ys

        semijoinGen <- mkExistentialSemiJoinT (x, xs) (y, ys) (Just q) (Just ps)
        return $ S semijoinGen

    _ -> fail "no match"

mkExistentialSemiJoinT :: (Ident, Expr) 
                       -> (Ident, Expr)
                       -> Maybe Expr
                       -> Maybe (NL Qual)
                       -> TransformC (NL Qual) Qual
mkExistentialSemiJoinT (x, xs) (y, ys) mq mps = do
    let yst = typeOf ys
        yt  = elemT yst

    -- All inner qualifiers have to be guards.
    guardExprs <- case mps of
        Just ps -> constT (T.mapM fromGuard ps) >>^ toList
        Nothing -> return []

    quantExprs <- case mq of
        Just q  -> constT (return $ inject q) >>> conjunctsT >>^ NL.toList
        Nothing -> return []

    let allExprs = guardExprs ++ quantExprs

    -- We demand at least one predicate expression
    guardM $ not $ null allExprs
        
    -- Separate those guards that can be evaluated just on the
    -- inner generator
    let (innerGuards, corrGuards) = partition (\e -> freeVars e == [y]) 
                                              allExprs

    let ys' = case innerGuards of
          ige : iges -> let igs = fmap GuardQ $ fromListSafe ige iges
                        in Comp yst (Var yt y) (BindQ y ys :* igs)
          []         -> ys

    corrPreds <- constT (return corrGuards) >>> mapT (splitJoinPredT x y)

    case corrPreds of
        cp : cps -> return $ BindQ x $ P.semijoin xs ys' (JoinPred $ cp :| cps)
        _        -> fail "there have to be correlation predicates for a semijoin"
 


existentialQualsR :: RewriteC (NL Qual)
existentialQualsR = onetdR existentialQualR

semijoinR :: RewriteC CL
semijoinR = do
    Comp _ _ _ <- promoteT idR
    childR CompQuals (promoteR existentialQualsR)
