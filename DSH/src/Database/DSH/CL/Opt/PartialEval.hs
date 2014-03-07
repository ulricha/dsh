{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE LambdaCase     #-}
    
-- | Support rewrites (partial evaluation, house cleaning)
module Database.DSH.CL.Opt.PartialEval
  ( houseCleaningR
  , partialEvalR
  ) where
  
import Debug.Trace

import           Control.Applicative
import           Control.Arrow
import           Control.Monad

import           Data.Maybe

import           Database.DSH.Common.Pretty
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.CL.Opt.Aux

------------------------------------------------------------------
-- Simple housecleaning support rewrites.
    
-- | Eliminate a map with an identity body
-- map (\x -> x) xs => xs
identityMapR :: RewriteC Expr
identityMapR = do
    AppE2 _ (Prim2 Map _) (Lam _ x (Var _ x')) xs <- idR
    guardM $ x == x'
    return xs
    
-- | Eliminate a comprehension with an identity head
-- [ x | x <- xs ] => xs
identityCompR :: RewriteC Expr
identityCompR = do
    Comp _ (Var _ x) (S (BindQ x' xs)) <- idR
    guardM $ x == x'
    return xs
    
-- | Eliminate tuple construction if the elements are first and second of the
-- same tuple:
-- pair (fst x) (snd x) => x
pairR :: RewriteC Expr
pairR = do
    AppE2 _ (Prim2 Pair _) (AppE1 _ (Prim1 Fst _) v@(Var _ x)) (AppE1 _ (Prim1 Snd _) (Var _ x')) <- idR
    guardM $ x == x'
    return v
    
houseCleaningR :: RewriteC CL
houseCleaningR = promoteR $ (identityMapR >>> debugTrace "identityMap")
                            <+ (identityCompR >>> debugTrace "identityCompR")
                            <+ (pairR >>> debugTrace "pair")
               
--------------------------------------------------------------------------------
-- Partial evaluation rules

fstR :: RewriteC Expr
fstR = do
    AppE1 _ (Prim1 Fst _) (AppE2 _ (Prim2 Pair _) e1 _) <- idR
    return e1

sndR :: RewriteC Expr
sndR = do
    AppE1 _ (Prim1 Snd _) (AppE2 _ (Prim2 Pair _) _ e2) <- idR
    return e2
    
partialEvalR :: RewriteC CL
partialEvalR = promoteR (fstR >>> debugTrace "fst")
               <+ promoteR (sndR >>> debugTrace "snd")
