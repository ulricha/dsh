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
    in AppE1 t (TupElem f) e

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

sng :: Expr -> Expr
sng x = AppE1 (listT $ typeOf x) Singleton x

concat :: Expr -> Expr
concat e = let t = typeOf e
            in if listDepth t P.> 1
               then AppE1 (unliftType t) Concat e
               else tyErrShow "concat" [t]

restrict :: Expr -> Expr
restrict xs = let ListT (TupleT [xt, BoolT]) = typeOf xs
              in AppE1 (ListT xt) Restrict xs

sort :: Expr -> Expr
sort xs = let ListT (TupleT [xt, _]) = typeOf xs
          in AppE1 (ListT xt) Sort xs

group :: Expr -> Expr
group xs = let ListT (TupleT [xt, gt]) = typeOf xs
           in AppE1 (ListT (TupleT [gt, ListT xt])) Group xs

let_ :: Ident -> Expr -> Expr -> Expr
let_ x e1 e2 = let t = typeOf e1 in Let t x e1 e2

if_ :: Expr -> Expr -> Expr -> Expr
if_ c t e = if BoolT == typeOf c
            then If (typeOf t) c t e
            else tyErr "if_"
