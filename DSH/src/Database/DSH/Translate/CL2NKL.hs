{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.CL2NKL
  ( desugarComprehensions ) where

import           Database.DSH.Impossible
       
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
              CL.Map            -> NKL.Map 
              CL.GroupWithKey   -> NKL.GroupWithKey
              CL.SortWith       -> NKL.SortWith 
              CL.Pair           -> NKL.Pair
              CL.Filter         -> NKL.Filter 
              CL.Append         -> NKL.Append
              CL.Index          -> NKL.Index 
              CL.Take           -> NKL.Take
              CL.Drop           -> NKL.Drop 
              CL.Zip            -> NKL.Zip
              CL.TakeWhile      -> NKL.TakeWhile
              CL.DropWhile      -> NKL.DropWhile
              CL.CartProduct    -> NKL.CartProduct
              CL.EquiJoin e1 e2 -> NKL.EquiJoin e1 e2
              CL.NestJoin e1 e2 -> NKL.NestJoin e1 e2
              CL.SemiJoin e1 e2 -> NKL.SemiJoin e1 e2
              CL.ConcatMap      -> $impossible

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
    -- Comprehensions with a single generator and only the bound variable in the
    -- head can be safely removed.
    (CL.Var _ x, CL.BindQ x' xs) | x == x' -> expr xs
  
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
  
  where e'  = CL.tuplify (x, xt) (y, yt) e
        qs' = CL.tuplifyQuals (x, xt) (y, yt) qs
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

-- | Express comprehensions in NKL iteration constructs map and concatMap.
desugarComprehensions :: CL.Expr -> NKL.Expr
desugarComprehensions = expr
