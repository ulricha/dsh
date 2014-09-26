-- | Smart constructors for NKL combinators
module Database.DSH.NKL.Primitives where

import           Prelude hiding (filter, map, concat, concatMap, fst, snd)
import qualified Prelude as P
import           Text.Printf

import           Database.DSH.Common.Type
import           Database.DSH.Common.Nat
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

tupElem :: TupleIndex -> Expr -> Expr
tupElem f e = 
    let t = tupleElemT (typeOf e) f
    in AppE1 t (Prim1 (TupElem f) (typeOf e .-> t)) e

fst :: Expr -> Expr
fst e = tupElem First e

snd :: Expr -> Expr
snd e = tupElem (Next First) e

pair :: Expr -> Expr -> Expr
pair a b = tuple [a, b]

tuple :: [Expr] -> Expr
tuple es =
    let ts = P.map typeOf es
        rt = TupleT ts
    in MkTuple rt es

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

let_ :: Ident -> Expr -> Expr -> Expr
let_ x e1 e2 = let t = typeOf e1 in Let t x e1 e2
