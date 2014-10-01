module Database.DSH.CL.Resugar
    ( resugarComprehensions
    ) where
       
import           Database.DSH.Impossible

import           Database.DSH.CL.Lang(NL(..))
import qualified Database.DSH.CL.Lang as CL
import           Database.DSH.CL.Opt.Aux
import qualified Database.DSH.CL.Primitives as CP
import qualified Database.DSH.Common.Type as T
import qualified Database.DSH.Common.Lang as L

import           Database.DSH.Frontend.Internals
import           Data.Text (unpack)

import qualified Data.Map as M

import           Control.Monad
import           Control.Monad.State
import           Control.Applicative
       
import           Text.Printf
  
import           GHC.Exts(sortWith)

-- | Restore the original comprehension form from the desugared concatMap form.
resugarComprehensions :: CL.Expr -> CL.Expr
resugarComprehensions = resugar

resugar :: CL.Expr -> CL.Expr
resugar expr = 
  case expr of 
    tab@(CL.Table _ _ _ _) -> tab
    CL.App t e1 e2 -> CL.App t (resugar e1) (resugar e2)

    -- This does not originate from a source comprehension, but is a
    -- normalization step to get as much as possible into comprehension form
    -- map (\x -> body) xs => [ body | x <- xs ]
    CL.AppE2 t CL.Map (CL.Lam _ x body) xs ->
        let body' = resugar body
            xs'   = resugar xs
        in resugar $ CL.Comp t body' (S (CL.BindQ x xs'))
  
    -- Another normalization step: Transform filter combinators to
    -- comprehensions
    -- filter (\x -> p) xs => [ x | x <- xs, p ]
    CL.AppE2 t CL.Filter (CL.Lam (T.FunT xt _) x p) xs ->
        let xs' = resugar xs
            p'  = resugar p
        in resugar $ CL.Comp t (CL.Var xt x) (CL.BindQ x xs' :* (S $ CL.GuardQ p'))
        
    CL.AppE1 t p1 e1 -> CL.AppE1 t p1 (resugar e1)
    
    -- (Try to) transform concatMaps into comprehensions
    cm@(CL.AppE2 t CL.ConcatMap body xs) ->
      let xs' = resugar xs
          body' = resugar body
      in 
    
      case body' of
        -- concatMap (\x -> [e]) xs
        -- => [ e | x < xs ]
        CL.Lam _ v (CL.AppE2 _ CL.Cons e (CL.Lit _ (L.ListV []))) ->
          resugar $ CL.Comp t e (S (CL.BindQ v xs'))

        -- Same case as above, just with a literal list in the lambda body.
        CL.Lam _ v (CL.Lit lt (L.ListV [s])) -> 
          resugar $ CL.Comp t (CL.Lit (CL.elemT lt) s) (S (CL.BindQ v xs'))

        -- concatMap (\x -> [ e | qs ]) xs
        -- => [ e | x <- xs, qs ]
        CL.Lam _ v (CL.Comp _ e qs) ->
          resugar $ CL.Comp t e (CL.BindQ v xs' :* qs)
          
        _ -> cm

    CL.AppE2 t p1 e1 e2 -> CL.AppE2 t p1 (resugar e1) (resugar e2)
    CL.BinOp t op e1 e2 -> CL.BinOp t op (resugar e1) (resugar e2)
    CL.UnOp t op e -> CL.UnOp t op (resugar e)
    CL.Lam t v e1 -> CL.Lam t v (resugar e1)
    
    CL.If t ce te ee -> CL.If t (resugar ce) (resugar te) (resugar ee)
    constant@(CL.Lit _ _)    -> constant
    var@(CL.Var _ _) -> var
    comp@(CL.Comp t body qs) -> 
      if changed 
      then resugar $ CL.Comp t body' qs'
      else CL.Comp t body' qs

      where 
        -- We fold over the qualifiers and look for local rewrite possibilities
        resugarQual :: CL.Qual -> Either CL.Qual CL.Qual
        resugarQual q = 
            case q of
                -- Eliminate unused bindings from guards
                -- qs, v <- guard p, qs'  => qs, p, qs' (when v \nelem fvs)
                CL.BindQ v (CL.AppE1 _ CL.Guard p) | not $ v `elem` fvs -> Right (CL.GuardQ p)
                -- This really sucks. employ proper change detection.
                CL.GuardQ p                                                          ->
                   let p' = resugar p in
                   if p' == p
                   then Left q
                   else Right (CL.GuardQ p')
                CL.BindQ x xs                                                        ->
                   let xs' = resugar xs in
                   if xs' == xs
                   then Left q
                   else Right (CL.BindQ x xs')
      
        qse     = fmap resugarQual qs
        changed = any isRight $ CL.toList qse
        qs'     = fmap (either id id) qse
      
        body'   = resugar body
        fvs     = freeVars comp
        
        isRight :: Either a b -> Bool
        isRight (Right _) = True
        isRight (Left _)  = False
            
