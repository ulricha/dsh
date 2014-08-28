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

concat :: Expr -> Expr
concat e = let t = typeOf e
            in if listDepth t P.> 1
               then AppE1 (unliftType t) (Prim1 Concat P.$ t .-> unliftType t) e
               else tyErrShow "concat" [t]

restrict :: Expr -> Expr -> Expr
restrict vs bs = let bst@(ListT BoolT) = typeOf bs
                     vst@(ListT _)     = typeOf vs
                 in AppE2 vst (Prim2 Restrict (vst .-> bst .-> vst)) vs bs

sort :: Expr -> Expr -> Expr
sort ss vs = let sst@(ListT _) = typeOf ss
                 vst@(ListT _) = typeOf vs
             in AppE2 vst (Prim2 Sort (sst .-> vst .-> vst)) ss vs

group :: Expr -> Expr -> Expr
group gs vs = let gst@(ListT _) = typeOf gs
                  vst@(ListT _) = typeOf vs
              in AppE2 vst (Prim2 Group (gst .-> vst .-> vst)) gs vs
