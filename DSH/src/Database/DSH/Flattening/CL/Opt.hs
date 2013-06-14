{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
    
-- | This module performs optimizations on the Nested Kernel Language (CL).
module Database.DSH.Flattening.CL.Opt 
  ( opt 
  ) where
       
import           Debug.Trace
import           Text.Printf

import           Data.Generics.Uniplate.Data
                 
import qualified Data.Set as S

import Database.DSH.Flattening.Common.Data.Val
import Database.DSH.Flattening.Common.Data.Op
import Database.DSH.Flattening.CL.Lang
       
-- Restore the original comprehension form from the desugared concatMap form.
normalize :: Expr -> Expr
normalize expr = 
  case expr of 
    tab@(Table _ _ _ _) -> tab
    App t e1 e2 -> App t (normalize e1) (normalize e2)

    AppE1 t p1 e1 -> AppE1 t p1 (normalize e1)
    
    cm@(AppE2 t (Prim2 ConcatMap _) body xs) ->
      let xs' = normalize xs
      in 
    
      case normalize body of
        -- concatMap (\x -> [e]) xs
        -- => [ e | x < xs ]
        Lam _ v (BinOp _ Cons e (Const _ (ListV []))) ->
          normalize $ Comp t e [BindQ v xs']

        -- concatMap (\x -> [ e | qs ]) xs
        -- => [ e | x <- xs, qs ]
        Lam _ v (Comp _ e qs) ->
          normalize $ Comp t e (BindQ v xs' : qs)
          
        _ -> cm

    AppE2 t p1 e1 e2 -> AppE2 t p1 (normalize e1) (normalize e2)
    BinOp t op e1 e2 -> BinOp t op (normalize e1) (normalize e2)
    Lam t v e1 -> Lam t v (normalize e1)
    
    If t ce te ee -> If t (normalize ce) (normalize te) (normalize ee)
    constant@(Const _ _) -> constant
    var@(Var _ _) -> var
    comp@(Comp t body qs) -> 
      if changed 
      then normalize $ Comp t body' qs'
      else Comp t body' qs

      where -- We fold over the qualifiers and look for local rewrite possibilities
            normalizeQual :: Qualifier -> (Bool, [Qualifier]) -> (Bool, [Qualifier])
            normalizeQual q (changedAcc, qsAcc) =
              case q of
                -- qs, v <- guard p, qs'  => qs, p, qs' (when v \nelem fvs)
                BindQ v (AppE1 _ (Prim1 Guard _) p) | not $ v `S.member` fvs -> (True, GuardQ p : qsAcc)
                _                                                            -> (changedAcc, q : qsAcc)
                
            (changed, qs') = foldr normalizeQual (False, []) qs
            body' = normalize body
            fvs = freeVars comp
  
pushFilters :: Expr -> Expr
pushFilters expr = transform go expr
  where go :: Expr -> Expr
        go (Comp t e qs) = Comp t e (reverse $ pushFromEnd $ reverse qs)
        go e             = e
        
        pushFromEnd :: [Qualifier] -> [Qualifier]
        pushFromEnd []                                   = []
        pushFromEnd ((GuardQ p) : qs) | isEquiJoinPred p = pushDown p (pushFromEnd qs)
        pushFromEnd (q : qs)                             = q : (pushFromEnd qs)
        
        pushDown :: Expr -> [Qualifier] -> [Qualifier]
        pushDown p []                                          = [GuardQ p]

        -- We push past other guards to get our join predicate as deep down as possible
        pushDown p (GuardQ p' : qs)                            = GuardQ p' : (pushDown p qs)

        -- We can't push past a generator on which the predicate depends
        pushDown p (BindQ x xs : qs) | x `S.member` freeVars p = (GuardQ p) : (BindQ x xs) : qs

        -- We push below generators if the predicate does not depend on it
        pushDown p (BindQ x xs : qs) | otherwise               = (BindQ x xs) : (pushDown p qs)
        
        isEquiJoinPred :: Expr -> Bool
        isEquiJoinPred (BinOp _ Eq e1 e2) = isProj e1 && isProj e2
        isEquiJoinPred _                  = False
        
        isProj :: Expr -> Bool
        isProj (AppE1 _ (Prim1 Fst _) e) = isProj e
        isProj (AppE1 _ (Prim1 Snd _) e) = isProj e
        isProj (Var _ _)               = True
        isProj _                       = False
            
opt :: Expr -> Expr
opt e = if (e /= e') 
        then trace (printf "%s\n---->\n%s" (show e) (show e')) e'
        else trace (show e) e'
  where e' = pushFilters $ normalize e
