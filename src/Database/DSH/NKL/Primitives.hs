-- | Smart constructors for NKL combinators
module Database.DSH.NKL.Primitives where

import Debug.Trace

import           Prelude hiding (filter, map, concat, concatMap, fst, snd)
import qualified Prelude as P
import           Text.Printf

import           Database.DSH.Common.Type
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Lang
import           Database.DSH.NKL.Lang

--------------------------------------------------------------------------------
-- Error reporting

tyErr :: P.String -> a
tyErr comb = P.error $ printf "CL.Primitives type error in %s" comb

tyErrShow :: P.String -> [Type] -> a
tyErrShow comb ts = P.error (printf "CL.Primitives type error in %s: %s" comb (P.show P.$ P.map pp ts))

--------------------------------------------------------------------------------
-- Smart constructors

fst :: Expr -> Expr
fst e = let t@(PairT t1 _) = typeOf e
         in AppE1 t1 (Prim1 Fst P.$ t .-> t1) e

snd :: Expr -> Expr
snd e = let t@(PairT _ t2) = typeOf e
         in AppE1 t2 (Prim1 Snd P.$ t .-> t2) e

pair :: Expr -> Expr -> Expr
pair (Const t1 v1) (Const t2 v2) = Const (pairT t1 t2) (PairV v1 v2)
pair e1 e2 = let t1 = typeOf e1
                 t2 = typeOf e2
              in AppE2 (pairT t1 t2) (Prim2 Pair P.$ t1 .-> t2 .-> pairT t1 t2) e1 e2

cons :: Expr -> Expr -> Expr
cons x xs = let xt  = typeOf x
                xst = typeOf xs
            in if elemT xst == xt
               then AppE2 xst (Prim2 Cons (xt .-> xst .-> xst)) x xs
               else tyErr "cons"

singleton :: Expr -> Expr
singleton e = let t = typeOf e in cons e (Const (listT t) (ListV []))

map :: Expr -> Expr -> Expr
map f es = let ft@(FunT ta tr) = typeOf f
               te@(ListT t)    = typeOf es
            in if t P.== ta
                 then AppE2 (listT tr) (Prim2 Map P.$ ft .-> te .-> listT tr) f es
                 else tyErr "map"

concatMap :: Expr -> Expr -> Expr
concatMap f xs = trace (printf "concatMap %s %s" (pp $ typeOf f) (pp $ typeOf xs)) $ concat $ map f xs

concat :: Expr -> Expr
concat e = let t = typeOf e
            in if listDepth t P.> 1
               then AppE1 (unliftType t) (Prim1 Concat P.$ t .-> unliftType t) e
               else tyErrShow "concat" [t]

filter :: Expr -> Expr -> Expr
filter f es = let ft@(FunT _ BoolT) = typeOf f
                  te@(ListT _) = typeOf es
               in AppE2 te (Prim2 Filter P.$ ft .-> te .-> te) f es
