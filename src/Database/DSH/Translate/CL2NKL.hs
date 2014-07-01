{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE BangPatterns     #-}

module Database.DSH.Translate.CL2NKL
  ( desugarComprehensions ) where

#ifdef DEBUG
import           Debug.Trace
import           Database.DSH.Common.Pretty
#endif
  
import           Database.DSH.Impossible
       
import           Database.DSH.Common.Type
import           Database.DSH.Common.Lang

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang(toList, fromList)
import qualified Database.DSH.CL.Lang as CL
import           Database.DSH.CL.Opt.Aux
import qualified Database.DSH.CL.Primitives as CP
import qualified Database.DSH.NKL.Lang as NKL
       
-- To transform CL into NKL we have to get rid of comprehensions. However, we
-- don't want to implement full comprehension desugaring. To avoid it, we
-- transform via an intermediate step: comprehensions with multiple generators
-- are transformed into comprehensions with one generator, where the nested
-- iterations are expressed in the form of cartesian products. The resulting
-- single-qualifier comprehension should then be easy to desugar (just a map).

prim1 :: Type -> CL.Prim1 Type -> CL.Expr -> NKL.Expr
prim1 t (CL.Prim1 o ot) e = mkApp t ot (expr e)
  where 
    mkApp = 
        case o of
            CL.Length           -> mkPrim1 NKL.Length 
            CL.Concat           -> mkPrim1 NKL.Concat 
            -- Null in explicit form is useful during CL optimization
            -- to easily recognize universal/existential patterns. In
            -- backend implementations however, there currently is no
            -- need to store it explicitly. Therefore, we implement it
            -- using length in NKL.
            CL.Null             -> nklLength
            CL.Sum              -> mkPrim1 NKL.Sum 
            CL.Avg              -> mkPrim1 NKL.Avg 
            CL.The              -> mkPrim1 NKL.The 
            CL.Fst              -> mkPrim1 NKL.Fst 
            CL.Snd              -> mkPrim1 NKL.Snd 
            CL.Head             -> mkPrim1 NKL.Head 
            CL.Minimum          -> mkPrim1 NKL.Minimum 
            CL.Maximum          -> mkPrim1 NKL.Maximum 
            CL.Tail             -> mkPrim1 NKL.Tail 
            CL.Reverse          -> mkPrim1 NKL.Reverse 
            CL.And              -> mkPrim1 NKL.And 
            CL.Or               -> mkPrim1 NKL.Or 
            CL.Init             -> mkPrim1 NKL.Init 
            CL.Last             -> mkPrim1 NKL.Last 
            CL.Nub              -> mkPrim1 NKL.Nub 
            CL.Number           -> mkPrim1 NKL.Number 
            (CL.Reshape n)      -> mkPrim1 $ NKL.Reshape n
            CL.Transpose        -> mkPrim1 NKL.Transpose
            CL.Guard            -> $impossible
    
    nklLength _ _ ne = NKL.BinOp boolT 
                                 (SBRelOp Eq)
                                 (NKL.Const intT $ IntV 0)
                                 (NKL.AppE1 intT 
                                            (NKL.Prim1 NKL.Length (typeOf ne .-> intT)) 
                                            ne)
                                       
    mkPrim1 nop nt nopt ne = NKL.AppE1 nt (NKL.Prim1 nop nopt) ne
                                   

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
              CL.Zip          -> NKL.Zip
              CL.Cons         -> NKL.Cons
              CL.CartProduct  -> NKL.CartProduct
              CL.NestProduct  -> NKL.NestProduct
              CL.ThetaJoin p  -> NKL.ThetaJoin p
              CL.NestJoin p   -> NKL.NestJoin p
              CL.SemiJoin p   -> NKL.SemiJoin p
              CL.AntiJoin p   -> NKL.AntiJoin p
              CL.ConcatMap    -> $impossible

expr :: CL.Expr -> NKL.Expr
expr (CL.Table t s cs ks)        = NKL.Table t s cs ks
expr (CL.App t e1 e2)            = NKL.App t (expr e1) (expr e2)
expr (CL.AppE1 t p e)            = prim1 t p e
expr (CL.AppE2 _ (CL.Prim2 CL.ConcatMap _) f xs) = expr $ CP.concat $ CP.map f xs
expr (CL.AppE2 t p e1 e2)        = NKL.AppE2 t (prim2 p) (expr e1) (expr e2)
expr (CL.BinOp t o e1 e2)        = NKL.BinOp t o (expr e1) (expr e2)
expr (CL.UnOp t o e)             = NKL.UnOp t o (expr e)
expr (CL.Lam t v e)              = NKL.Lam t v (expr e)
expr (CL.If t c th el)           = NKL.If t (expr c) (expr th) (expr el)
expr (CL.Lit t v)                = NKL.Const t v
expr (CL.Var t v)                = NKL.Var t v
expr (CL.Comp t e qs)            = desugar t e (toList qs)
     
-- FIXME it would be nice to encode the non-emptiness of qualifier lists in the
-- types. Currently, that's rather messy.

-- | Desugar comprehensions into NKL expressions
desugar :: Type -> CL.Expr -> [CL.Qual] -> NKL.Expr
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
    
    (e', CL.GuardQ p)   -> expr $ CL.If t p (CL.AppE2 t (CL.Prim2 CL.Cons consTy) e' empty) empty
      where 
        empty  = CL.Lit t (ListV [])
        consTy = elemT t .-> t .-> t

-- | Turn multiple qualifiers into one qualifier using cartesian products and
-- filters to express nested iterations and predicates.
productify :: CL.Expr -> [CL.Qual] -> (CL.Expr, CL.Qual)
productify _ []                                 = $impossible
productify e [q]                                = (e, q)
           
-- [ e | x <- xs, y <- ys, qs ] = 
-- [ e[fst x/x][snd x/y] | x <- cartProd xs ys, qs[fst x/x][snd x/y] ]
productify e ((CL.BindQ x xs) : (CL.BindQ y ys) : qs) = 
    productify e' (q' : qs')
  
  where e'  = guardTuplify x (x, xt) (y, yt) e
        qs' = case fromList qs of
                  Nothing    -> []
                  Just qne   -> toList $ guardTuplify x (x, xt) (y, yt) qne
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

  where q' = CL.GuardQ $ CL.BinOp boolT (SBBoolOp Conj) p1 p2
           
-- [ e | p1, x <- xs, qs ] = [ e | x <- filter (\x -> p) xs, qs ]
-- FIXME this seems wrong
productify e ((CL.GuardQ p)   : (CL.BindQ x xs) : qs) = 
  productify e ((CL.GuardQ p) : (CL.BindQ x xs) : qs)
  
guardTuplify :: (Injection a CL, Show a) => Ident -> (Ident, Type) -> (Ident, Type) -> a -> a
guardTuplify x v1 v2 v = 
    case applyInjectable (tuplifyR x v1 v2) v of
        Left _   -> v
        Right v' -> maybe $impossible id (project v')
        
-- | Express comprehensions in NKL iteration constructs map and concatMap.
desugarComprehensions :: CL.Expr -> NKL.Expr
desugarComprehensions e = 
#ifdef DEBUG
    trace (debugPrint eo) eo

  where
    eo = expr e

    padSep :: String -> String
    padSep s = "\n" ++ s ++ " " ++ replicate (100 - length s) 'x'

    debugPrint :: NKL.Expr -> String
    debugPrint e' = padSep "Desugared NKL" ++ pp e' ++ padSep ""
#else
    expr e
#endif

