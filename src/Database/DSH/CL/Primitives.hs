{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Smart constructors for CL primitives
module Database.DSH.CL.Primitives where

import qualified Prelude                        as P

import qualified Data.List                      as List
import qualified Data.Time.Calendar             as C
import           Text.Printf
import           Data.Decimal

import           Database.DSH.CL.Lang
import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty

tyErr :: P.String -> a
tyErr comb = P.error P.$ printf "CL.Primitives type error in %s" comb

tyErrShow :: P.String -> [Type] -> a
tyErrShow comb ts = P.error (printf "CL.Primitives type error in %s: %s" comb (P.show P.$ P.map pp ts))

if_ :: Expr -> Expr -> Expr -> Expr
if_ c t e = if PBoolT P.== typeOf c
            then If (typeOf t) c t e
            else tyErr "if_"

reverse :: Expr -> Expr
reverse e = let t@(ListT _) = typeOf e
             in AppE1 t Reverse e

length :: Expr -> Expr
length e = let t = typeOf e
           in if isList t
              then AppE1 PIntT Length e
              else tyErr "length"

null :: Expr -> Expr
null e =
    if isList t
    then AppE1 PBoolT Null e
    else tyErr "null"

  where t = typeOf e

and :: Expr -> Expr
and e = let t = typeOf e
         in if ListT PBoolT P.== t
            then AppE1 PBoolT And e
            else tyErrShow "and" [t]

or :: Expr -> Expr
or e = let t = typeOf e
         in if ListT PBoolT P.== t
            then AppE1 PBoolT Or e
            else tyErr "or"

concat :: Expr -> Expr
concat e = let t = typeOf e
            in if listDepth t P.> 1
               then AppE1 (unliftType t) Concat e
               else tyErr "concat"

-- reshape :: [a] -> [[a]]
reshape :: P.Integer -> Expr -> Expr
reshape n e =
    let t = typeOf e
    in AppE1 (ListT t) (Reshape n) e

-- transpose :: [[a]] -> [[a]]
transpose :: Expr -> Expr
transpose e =
    let t = typeOf e
    in AppE1 t Transpose e

sum :: Expr -> Expr
sum e = let (ListT t) = typeOf e
         in if isNum t
                then AppE1 t Sum e
                else tyErr "sum"


avg :: Expr -> Expr
avg e = case typeOf e of
            ListT PDoubleT  -> AppE1 PDoubleT Avg e
            ListT PDecimalT -> AppE1 PDecimalT Avg e
            _              -> tyErr "avg"

minimum :: Expr -> Expr
minimum e = let (ListT t) = typeOf e
             in if isNum t
                 then AppE1 t Minimum e
                 else tyErr "minimum"

maximum :: Expr -> Expr
maximum e = let (ListT t) = typeOf e
             in if isNum t
                 then AppE1 t Maximum e
                 else tyErr "maximum"

the :: Expr -> Expr
the e = let (ListT t) = typeOf e
         in AppE1 t The e

head :: Expr -> Expr
head e = let (ListT t) = typeOf e
          in AppE1 t Head e

last :: Expr -> Expr
last e = let (ListT t) = typeOf e
          in AppE1 t Last e

tail :: Expr -> Expr
tail e = let (ListT t) = typeOf e
          in AppE1 (ListT t) Tail e

nub :: Expr -> Expr
nub e = let (ListT t) = typeOf e
         in AppE1 (ListT t) Nub e

number :: Expr -> Expr
number e = let (ListT t) = typeOf e
           in AppE1 (ListT (PPairT t PIntT )) Number e

guard :: Expr -> Expr
guard e = AppE1 (ListT PUnitT) Guard e

init :: Expr -> Expr
init e = let (ListT t) = typeOf e
        in AppE1 (ListT t) Init e

tupElem :: TupleIndex -> Expr -> Expr
tupElem f e =
    let t = tupleElemT (typeOf e) f
    in AppE1 t (TupElem f) e

fst :: Expr -> Expr
fst e = tupElem First e

snd :: Expr -> Expr
snd e = tupElem (Next First) e

singleGenComp :: Expr -> L.Ident -> Expr -> Expr
singleGenComp bodyExp v gen =
    let bodyTy = typeOf bodyExp
    in Comp (ListT bodyTy) bodyExp (S P.$ BindQ v gen)

group :: Expr -> Expr
group xs = let ListT (TupleT [xt, grt]) = typeOf xs
               rt                       = ListT (TupleT [grt, ListT xt])
           in AppE1 rt Group xs

sort :: Expr -> Expr
sort xs = let ListT (TupleT [xt, _]) = typeOf xs
          in AppE1 (ListT xt) Sort xs

pair :: Expr -> Expr -> Expr
pair a b = tuple [a, b]

tuple :: [Expr] -> Expr
tuple es =
    let ts = P.map typeOf es
        rt = TupleT ts
    in MkTuple rt es

append :: Expr -> Expr -> Expr
append e1 e2 = let t1@(ListT _) = typeOf e1
                   t2@(ListT _) = typeOf e2
                in if t1 P.== t2
                    then AppE2 t1 Append e1 e2
                    else tyErr "append"

index :: Expr -> Expr -> Expr
index e1 e2 = let ListT t = typeOf e1
                  t2 = typeOf e2
                in if PIntT P.== t2
                    then AppE2 t Index e1 e2
                    else tyErr "index"

sng :: Expr -> Expr
sng e = AppE1 (ListT P.$ typeOf e) Singleton e

zip :: Expr -> Expr -> Expr
zip e1 e2 = let ListT t1' = typeOf e1
                ListT t2' = typeOf e2
             in AppE2 (ListT P.$ PPairT t1' t2') Zip e1 e2

var :: Type -> P.String -> Expr
var = Var

table :: Type -> P.String -> L.BaseTableSchema -> Expr
table = Table

cond :: Expr -> Expr -> Expr -> Expr
cond eb et ee = let tb = typeOf eb
                    tt = typeOf et
                    te = typeOf ee
                 in if tb P.== PBoolT P.&& tt P.== te
                      then If te eb et ee
                      else tyErr "cond"

let_ :: L.Ident -> Expr -> Expr -> Expr
let_ x e1 e2 = let t = typeOf e2 in Let t x e1 e2

---------------------------------------------------------------------------------------
-- Smart constructors for join operators

cartproduct :: Expr -> Expr -> Expr
cartproduct xs ys = AppE2 resType CartProduct xs ys
  where
    resType  = ListT P.$ PPairT (elemT P.$ typeOf xs) (typeOf ys)

nestjoin :: Expr -> Expr -> L.JoinPredicate L.JoinExpr -> Expr
nestjoin xs ys p = AppE2 resType (NestJoin p) xs ys
  where
    resType  = ListT P.$ PPairT (elemT P.$ typeOf xs) (typeOf ys)

thetajoin :: Expr -> Expr -> L.JoinPredicate L.JoinExpr -> Expr
thetajoin xs ys p = AppE2 rt (ThetaJoin p) xs ys
  where
    xst = typeOf xs
    yst = typeOf ys
    rt  = ListT (PPairT (elemT xst) (elemT yst))

semijoin :: Expr -> Expr -> L.JoinPredicate L.JoinExpr -> Expr
semijoin xs ys p = AppE2 xst (SemiJoin p) xs ys
  where
    xst = typeOf xs

antijoin :: Expr -> Expr -> L.JoinPredicate L.JoinExpr -> Expr
antijoin xs ys p = AppE2 xst (AntiJoin p) xs ys
  where
    xst = typeOf xs

---------------------------------------------------------------------------------------
-- Literal value constructors

unit :: Expr
unit = Lit PUnitT (L.ScalarV L.UnitV)

int :: P.Int -> Expr
int i = Lit PIntT (L.ScalarV (L.IntV i))

bool :: P.Bool -> Expr
bool b = Lit PBoolT (L.ScalarV (L.BoolV b))

string :: P.String -> Expr
string s = Lit PStringT (L.ScalarV (L.StringV s))

double :: P.Double -> Expr
double d = Lit PDoubleT (L.ScalarV (L.DoubleV d))

decimal :: Decimal -> Expr
decimal d = Lit PDecimalT (L.ScalarV (L.DecimalV d))

day :: C.Day -> Expr
day d = Lit PDateT (L.ScalarV (L.DateV d))

nil :: Type -> Expr
nil t = Lit t (L.ListV [])

list :: Type -> [Expr] -> Expr
list _ (e : es) = List.foldl' append (sng e) (P.map sng es)
list t []       = nil t

cons :: Expr -> Expr -> Expr
cons e1 e2 = append (sng e1) e2

---------------------------------------------------------------------------------------
-- Smart constructors for scalar unary operators

scalarUnOp :: L.ScalarUnOp -> Expr -> Expr
scalarUnOp op e =
    let t = typeOf e
    in case (op, t) of
           (L.SUNumOp _, PDoubleT)                  -> UnOp t op e
           (L.SUBoolOp _, PBoolT)                   -> UnOp PBoolT op e
           (L.SUCastOp L.CastDouble, _) | isNum t  -> UnOp PDoubleT op e
           (L.SUCastOp L.CastDecimal, _) | isNum t -> UnOp PDecimalT op e
           (L.SUTextOp L.SubString{}, PStringT)     -> UnOp PStringT op e
           (L.SUDateOp _, PDateT)                   -> UnOp PIntT op e
           (_, _)                                  -> P.error err
               where err = printf "CL.Primitives.scalarUnOp: %s" (P.show (op, t))

castDouble :: Expr -> Expr
castDouble = scalarUnOp (L.SUCastOp L.CastDouble)

castDecimal :: Expr -> Expr
castDecimal = scalarUnOp (L.SUCastOp L.CastDecimal)

dateDay :: Expr -> Expr
dateDay = scalarUnOp (L.SUDateOp L.DateDay)

dateMonth :: Expr -> Expr
dateMonth = scalarUnOp (L.SUDateOp L.DateMonth)

dateYear :: Expr -> Expr
dateYear = scalarUnOp (L.SUDateOp L.DateYear)

not :: Expr -> Expr
not = scalarUnOp (L.SUBoolOp L.Not)

sin :: Expr -> Expr
sin = scalarUnOp (L.SUNumOp L.Sin)

cos :: Expr -> Expr
cos = scalarUnOp (L.SUNumOp L.Cos)

tan :: Expr -> Expr
tan = scalarUnOp (L.SUNumOp L.Tan)

asin :: Expr -> Expr
asin = scalarUnOp (L.SUNumOp L.ASin)

acos :: Expr -> Expr
acos = scalarUnOp (L.SUNumOp L.ACos)

atan :: Expr -> Expr
atan = scalarUnOp (L.SUNumOp L.ATan)

log :: Expr -> Expr
log = scalarUnOp (L.SUNumOp L.Log)

sqrt :: Expr -> Expr
sqrt = scalarUnOp (L.SUNumOp L.Sqrt)

exp :: Expr -> Expr
exp = scalarUnOp (L.SUNumOp L.Exp)

substring :: P.Integer -> P.Integer -> Expr -> Expr
substring f t = scalarUnOp (L.SUTextOp P.$ L.SubString f t)

---------------------------------------------------------------------------------
-- Smart constructors for scalar binary operators

-- | Type checking for binary operators
scalarBinOp :: L.ScalarBinOp -> Expr -> Expr -> Expr
scalarBinOp op e1 e2 =
    case (op, t1, t2) of
        (L.SBNumOp _, _, _)
            | t1 P.== t2 P.&& isNum t1 P.&& isNum t2 -> BinOp t1 op e1 e2
        (L.SBRelOp _, _, _)
            | t1 P.== t2                             -> BinOp PBoolT op e1 e2
        (L.SBBoolOp _, PBoolT, PBoolT)               -> BinOp PBoolT op e1 e2
        (L.SBStringOp L.Like, PStringT, PStringT)    -> BinOp PBoolT op e1 e2
        (L.SBDateOp L.AddDays, PIntT, PDateT)        -> BinOp PDateT op e1 e2
        (L.SBDateOp L.SubDays, PIntT, PDateT)        -> BinOp PDateT op e1 e2
        (L.SBDateOp L.DiffDays, PDateT, PDateT)      -> BinOp PIntT op e1 e2
        _                                            ->
            P.error P.$ printf "CL.Primitives.scalarBinOp: %s" (P.show (op, t1, t2))
  where
    t1 = typeOf e1
    t2 = typeOf e2

addDays :: Expr -> Expr -> Expr
addDays = scalarBinOp (L.SBDateOp L.AddDays)

subDays :: Expr -> Expr -> Expr
subDays = scalarBinOp (L.SBDateOp L.SubDays)

diffDays :: Expr -> Expr -> Expr
diffDays = scalarBinOp (L.SBDateOp L.DiffDays)

add :: Expr -> Expr -> Expr
add = scalarBinOp (L.SBNumOp L.Add)

sub :: Expr -> Expr -> Expr
sub = scalarBinOp (L.SBNumOp L.Sub)

mul :: Expr -> Expr -> Expr
mul = scalarBinOp (L.SBNumOp L.Mul)

div :: Expr -> Expr -> Expr
div = scalarBinOp (L.SBNumOp L.Div)

mod :: Expr -> Expr -> Expr
mod = scalarBinOp (L.SBNumOp L.Mod)

eq :: Expr -> Expr -> Expr
eq = scalarBinOp (L.SBRelOp L.Eq)

neq :: Expr -> Expr -> Expr
neq = scalarBinOp (L.SBRelOp L.NEq)

gt :: Expr -> Expr -> Expr
gt = scalarBinOp (L.SBRelOp L.Gt)

lt :: Expr -> Expr -> Expr
lt = scalarBinOp (L.SBRelOp L.Lt)

gte :: Expr -> Expr -> Expr
gte = scalarBinOp (L.SBRelOp L.GtE)

lte :: Expr -> Expr -> Expr
lte = scalarBinOp (L.SBRelOp L.LtE)

conj :: Expr -> Expr -> Expr
conj = scalarBinOp (L.SBBoolOp L.Conj)

disj :: Expr -> Expr -> Expr
disj = scalarBinOp (L.SBBoolOp L.Disj)

like :: Expr -> Expr -> Expr
like = scalarBinOp (L.SBStringOp L.Like)

