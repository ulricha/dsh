-- | Smart constructors for NKL combinators
module Database.DSH.NKL.Primitives where

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
tyErr comb = P.error $ printf "NKL.Primitives type error in %s" comb

tyErrShow :: P.String -> [Type] -> a
tyErrShow comb ts = P.error (printf "NKL.Primitives type error in %s: %s" comb (P.show P.$ P.map pp ts))

--------------------------------------------------------------------------------
-- Smart constructors

fst :: Expr -> Expr
fst e = let PairT t1 _ = typeOf e
         in AppE1 t1 Fst e

snd :: Expr -> Expr
snd e = let PairT _ t2 = typeOf e
         in AppE1 t2 Snd e

pair :: Expr -> Expr -> Expr
pair (Const t1 v1) (Const t2 v2) = Const (pairT t1 t2) (PairV v1 v2)
pair e1 e2 = let t1 = typeOf e1
                 t2 = typeOf e2
              in AppE2 (pairT t1 t2) Pair e1 e2

cons :: Expr -> Expr -> Expr
cons x xs = let xt  = typeOf x
                xst = typeOf xs
            in if elemT xst == xt
               then AppE2 xst Cons x xs
               else tyErr "cons"

singleton :: Expr -> Expr
singleton e = let t = typeOf e in cons e (Const (listT t) (ListV []))

concat :: Expr -> Expr
concat e = let t = typeOf e
            in if listDepth t P.> 1
               then AppE1 (unliftType t) Concat e
               else tyErrShow "concat" [t]

restrict :: Expr -> Expr -> Expr
restrict vs bs = let vst@(ListT _)     = typeOf vs
                 in AppE2 vst Restrict vs bs

sort :: Expr -> Expr -> Expr
sort ss vs = let vst@(ListT _) = typeOf vs
             in AppE2 vst Sort ss vs

group :: Expr -> Expr -> Expr
group gs vs = let vst@(ListT _) = typeOf vs
              in AppE2 vst Group gs vs

let_ :: Ident -> Expr -> Expr -> Expr
let_ x e1 e2 = let t = typeOf e1 in Let t x e1 e2
