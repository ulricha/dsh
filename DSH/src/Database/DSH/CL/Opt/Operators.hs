{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | Introduce additional operators (e.g. selection, projection)
module Database.DSH.CL.Opt.Operators
  ( selectR ) where
  
import           Debug.Trace
       
import           Control.Arrow

import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import           Database.DSH.CL.Opt.Aux

import qualified Database.DSH.CL.Primitives as P

--------------------------------------------------------------------------------
-- Filter pushdown

selectQualsR :: (Expr -> Bool) -> RewriteC (NL Qual)
selectQualsR mayPush = prunetdR $ pushR <+ pushEndR
  where
    mkselectM :: Ident -> Expr -> Expr -> CompM Int Qual
    mkselectM x xs p = do
        -- We only push predicates into generators if the predicate depends
        -- solely on this generator
        let fvs = freeVars p
        guardM $ [x] == fvs
        
        -- Only push filters which the 'mayPush' predicate considers eligible.
        guardM $ mayPush p
        
        -- We do not push filters onto comprehensions. A comprehension nested in
        -- a qualifier needs to be unnested via m_norm_3 first. We add this
        -- safeguard because we want to push filters early but need to avoid
        -- blocking m_norm_3.
        case xs of
            Comp _ _ _ -> fail "selectR: don't push filters onto comprehensions"
            _          -> return ()
            
        return $ BindQ x (P.filter (Lam ((elemT $ typeOf xs) .-> boolT) x p) xs)
        

    pushR :: RewriteC (NL Qual)
    pushR = do
        (BindQ x xs) :* GuardQ p :* qs <- idR
        
        q' <- constT $ mkselectM x xs p
        
        return $ q' :* qs
        
        
    pushEndR :: RewriteC (NL Qual)
    pushEndR = do
        (BindQ x xs) :* (S (GuardQ p)) <- idR
        
        q' <- constT $ mkselectM x xs p
        
        return $ S q'
        
selectR :: ([Ident] -> Expr -> Bool) -> RewriteC CL
selectR mayPush = do
    Comp t h qs <- promoteT idR
    let localScope = compBoundVars $ toList qs
    qs' <- childT 1 (promoteR (selectQualsR (mayPush localScope)) >>> projectT)
    trace "select" $ return $ inject $ Comp t h qs'
