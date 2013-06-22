{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.CL2NKL
  ( desugarComprehensions ) where
       
import           Database.DSH.Impossible
       
import           Database.DSH.Common.Data.Expr
import           Database.DSH.Common.Data.Type
import           Database.DSH.Common.Data.Val
import           Database.DSH.Common.Data.Op

import qualified Database.DSH.CL.Lang as CL
import qualified Database.DSH.NKL.Data.NKL as NKL
import qualified Database.DSH.CL.Primitives as CP
       
-- To transform CL into NKL we have to get rid of comprehensions. However, we
-- don't want to implement full comprehension desugaring. To avoid it, we
-- transform via an intermediate step: comprehensions with multiple generators
-- are transformed into comprehensions with one generator, where the nested
-- iterations are expressed in the form of cartesian products. The resulting
-- single-qualifier comprehension should then be easy to desugar (just a map).

prim1 :: CL.Prim1 Type -> NKL.Prim1 Type
prim1 (CL.Prim1 o t) = NKL.Prim1 o' t
  where o' = case o of
               CL.Length           -> NKL.Length 
               CL.Not              -> NKL.Not 
               CL.Concat           -> NKL.Concat 
               CL.Sum              -> NKL.Sum 
               CL.Avg              -> NKL.Avg 
               CL.The              -> NKL.The 
               CL.Fst              -> NKL.Fst 
               CL.Snd              -> NKL.Snd 
               CL.Head             -> NKL.Head 
               CL.Minimum          -> NKL.Minimum 
               CL.Maximum          -> NKL.Maximum 
               CL.IntegerToDouble  -> NKL.IntegerToDouble 
               CL.Tail             -> NKL.Tail 
               CL.Reverse          -> NKL.Reverse 
               CL.And              -> NKL.And 
               CL.Or               -> NKL.Or 
               CL.Init             -> NKL.Init 
               CL.Last             -> NKL.Last 
               CL.Nub              -> NKL.Nub 
               CL.Number           -> NKL.Number 
               CL.Guard            -> $impossible

prim2 :: CL.Prim2 Type -> NKL.Prim2 Type
prim2 (CL.Prim2 o t) = NKL.Prim2 o' t
  where o' = case o of
              CL.Map          -> NKL.Map 
              CL.GroupWithKey -> NKL.GroupWithKey
              CL.SortWith     -> NKL.SortWith 
              CL.Pair         -> NKL.Pair
              CL.Filter       -> NKL.Filter 
              CL.Append       -> NKL.Append
              CL.Index        -> NKL.Index 
              CL.Take         -> NKL.Take
              CL.Drop         -> NKL.Drop 
              CL.Zip          -> NKL.Zip
              CL.TakeWhile    -> NKL.TakeWhile
              CL.DropWhile    -> NKL.DropWhile
              CL.CartProduct  -> NKL.CartProduct
              CL.ConcatMap    -> $impossible

expr :: CL.Expr -> NKL.Expr
expr (CL.Table t s cs ks) = NKL.Table t s cs ks
expr (CL.App t e1 e2)     = NKL.App t (expr e1) (expr e2)
expr (CL.AppE1 t p e)     = NKL.AppE1 t (prim1 p) (expr e)
expr (CL.AppE2 _ (CL.Prim2 CL.ConcatMap _) f xs) = expr $ CP.concat $ CP.map f xs
expr (CL.AppE2 t p e1 e2) = NKL.AppE2 t (prim2 p) (expr e1) (expr e2)
expr (CL.BinOp t o e1 e2) = NKL.BinOp t o (expr e1) (expr e2)
expr (CL.Lam t v e)       = NKL.Lam t v (expr e)
expr (CL.If t c th el)    = NKL.If t (expr c) (expr th) (expr el)
expr (CL.Const t v)       = NKL.Const t v
expr (CL.Var t v)         = NKL.Var t v
expr (CL.Comp t e qs)     = desugar t e qs

-- | Desugar comprehensions into NKL expressions
desugar :: Type -> CL.Expr -> [CL.Qualifier] -> NKL.Expr
desugar t e qs =
  -- We reduce a comprehension with multiple qualifiers to a comprehension with
  -- one qualifier, which we can then handle easily.
  case productify e qs of 
    (e', CL.BindQ x xs) -> expr $ CP.map (CL.Lam (xt .-> rt) x e') xs
      where xt = elemT $ typeOf xs
            rt = elemT t
    (e', CL.GuardQ p)   -> expr $ CL.If t p (CL.BinOp t Cons e' empty) empty
      where empty = CL.Const t (ListV [])

-- | Turn multiple qualifiers into one qualifier using cartesian products and
-- filters to express nested iterations and predicates.
productify :: CL.Expr -> [CL.Qualifier] -> (CL.Expr, CL.Qualifier)
productify e []                                 = $impossible
productify e [q]                                = (e, q)
           
-- [ e | x <- xs, y <- ys, qs ] = 
-- [ e[fst x/x][snd x/y] | x <- cartProd xs ys, qs[fst x/x][snd x/y] ]
productify e ((CL.BindQ x xs) : (CL.BindQ y ys) : qs) = 
  productify e' (q' : qs')
  
  where e'  = tuplify (x, xt) (y, yt) e
        qs' = tuplifyQuals (x, xt) (y, yt) qs
        q'  = CL.BindQ x (CL.AppE2 (listT pt) (CL.Prim2 CL.CartProduct cpt) xs ys)
        xt  = elemT $ typeOf xs
        yt  = elemT $ typeOf ys 
        pt  = pairT xt yt
        cpt = xt .-> (yt .-> listT pt)

-- [ e | x <- xs, p, qs ] = [ e | x <- filter (\x -> p) xs, qs ]
productify e ((CL.BindQ x xs) : (CL.GuardQ p)   : qs) = 
  productify e (q' : qs)

  where q'  = CL.BindQ x (CL.AppE2 (listT xt) (CL.Prim2 CL.Filter ft) (CL.Lam (xt .-> boolT) x p) xs)
        ft  = (xt .-> boolT) .-> (xst .-> xst)
        xst = typeOf xs
        xt  = elemT xst
           
-- [ e | p1, p2, qs ] = [ e | p1 && p2, qs ]
productify e ((CL.GuardQ p1)  : (CL.GuardQ p2)  : qs) = 
  productify e (q' : qs)

  where q' = CL.GuardQ $ CL.BinOp boolT Conj p1 p2
           
-- [ e | p1, x <- xs, qs ] = [ e | x <- filter (\x -> p) xs, qs ]
productify e ((CL.GuardQ p)   : (CL.BindQ x xs) : qs) = 
  productify e ((CL.GuardQ p) : (CL.BindQ x xs) : qs)

-- | Substitution: subst v r e ~ e[v/r]
subst :: Ident -> CL.Expr -> CL.Expr -> CL.Expr
subst _ _ table@(CL.Table _ _ _ _) = table
subst v r (CL.App t e1 e2)         = CL.App t (subst v r e1) (subst v r e2)
subst v r (CL.AppE1 t p e)         = CL.AppE1 t p (subst v r e)
subst v r (CL.AppE2 t p e1 e2)     = CL.AppE2 t p (subst v r e1) (subst v r e2)
subst v r (CL.BinOp t o e1 e2)     = CL.BinOp t o (subst v r e1) (subst v r e2)
-- FIXME for the moment, we assume that all lambda variables are unique
-- and we don't need to check for name capturing/do alpha-conversion.
subst v r lam@(CL.Lam t v' e)      = if v' == v
                                     then lam
                                     else CL.Lam t v' (subst v r e)
subst _ _ c@(CL.Const _ _)         = c
subst v r var@(CL.Var _ v')        = if v == v' then r else var
subst v r (CL.If t c thenE elseE)  = CL.If t (subst v r c) (subst v r thenE) (subst v r elseE)
subst v r (CL.Comp t e qs)         = CL.Comp t (subst v r e) (substQuals v r qs)

-- | Substitution on a list of qualifiers
substQuals :: Ident -> CL.Expr -> [CL.Qualifier] -> [CL.Qualifier]
substQuals v r ((CL.GuardQ g) : qs)               = (CL.GuardQ (subst v r g)) : (substQuals v r qs)
substQuals v r ((CL.BindQ v' s) : qs) | v == v'   = (CL.BindQ v' (subst v r s)) : qs
substQuals v r ((CL.BindQ v' s) : qs) | otherwise = (CL.BindQ v' (subst v r s)) : (substQuals v r qs)
substQuals _ _ []                                 = []

-- tuplify v1 v2 e = e[v1/fst v1][v2/snd v1]
tuplify :: (Ident, Type) -> (Ident, Type) -> CL.Expr -> CL.Expr
tuplify (v1, t1) (v2, t2) e = subst v2 v2Rep $ subst v1 v1Rep e

  where (v1Rep, v2Rep) = tupleVars (v1, t1) (v2, t2)

tuplifyQuals :: (Ident, Type) -> (Ident, Type) -> [CL.Qualifier] -> [CL.Qualifier]
tuplifyQuals (v1, t1) (v2, t2) qs = substQuals v2 v2Rep $ substQuals v1 v1Rep qs

  where (v1Rep, v2Rep) = tupleVars (v1, t1) (v2, t2)

tupleVars :: (Ident, Type) -> (Ident, Type) -> (CL.Expr, CL.Expr)
tupleVars (v1, t1) (_, t2) = (v1Rep, v2Rep)
  where v1'    = CL.Var pt v1
        pt     = pairT t1 t2
        v1Rep  = CL.AppE1 t1 (CL.Prim1 CL.Fst (pt .-> t1)) v1'
        v2Rep  = CL.AppE1 t2 (CL.Prim1 CL.Snd (pt .-> t2)) v1'

-- | Express comprehensions in NKL iteration constructs map and concatMap.
desugarComprehensions :: CL.Expr -> NKL.Expr
desugarComprehensions = expr
