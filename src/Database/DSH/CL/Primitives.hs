{-# LANGUAGE TemplateHaskell #-}

-- | Smart constructors for CL primitives
module Database.DSH.CL.Primitives where

import qualified Prelude                  as P

import           Text.Printf
import           Debug.Trace

import           Database.DSH.CL.Lang
import qualified Database.DSH.Common.Lang as L
import           Database.DSH.Impossible
import           Database.DSH.Common.Pretty

tyErr :: P.String -> a
tyErr comb = P.error ("CL.Primitives type error in %s" P.++ comb)

tyErrShow :: P.String -> [Type] -> a
tyErrShow comb ts = P.error (printf "CL.Primitives type error in %s: %s" comb (P.show P.$ P.map pp ts))

($) :: Expr -> Expr -> Expr
f $ e = let tf = typeOf f
            te = typeOf e
            (ta, tr) = splitType tf
         in if ta P.== te
              then App tr f e
              else tyErr "$"

reverse :: Expr -> Expr
reverse e = let t@(ListT _) = typeOf e
             in AppE1 t (Prim1 Reverse P.$ t .-> t) e

length :: Expr -> Expr
length e = let t = typeOf e
           in if isList t
              then AppE1 intT (Prim1 Length P.$ t .-> intT) e
              else tyErr "length"

all :: Expr -> Expr -> Expr
all f e = and (map f e)

any :: Expr -> Expr -> Expr
any f e = or (map f e)

null :: Expr -> Expr
null e =
    if isList t
    then AppE1 boolT (Prim1 Null P.$ t .-> boolT) e
    else tyErr "null"

  where t = typeOf e

and :: Expr -> Expr
and e = let t = typeOf e
         in if listT boolT P.== t
            then AppE1 boolT (Prim1 And P.$ t .-> boolT) e
            else tyErrShow "and" [t]

or :: Expr -> Expr
or e = let t = typeOf e
         in if listT boolT P.== t
            then AppE1 boolT (Prim1 Or P.$ t .-> boolT) e
            else tyErr "or"

concat :: Expr -> Expr
concat e = let t = typeOf e
            in if listDepth t P.> 1
               then AppE1 (unliftType t) (Prim1 Concat P.$ t .-> unliftType t) e
               else tyErr "concat"

-- reshape :: [a] -> [[a]]
reshape :: P.Integer -> Expr -> Expr
reshape n e =
    let t = typeOf e
    in AppE1 (ListT t) (Prim1 (Reshape n) P.$ t .-> ListT t) e

-- transpose :: [[a]] -> [[a]]
transpose :: Expr -> Expr
transpose e =
    let t = typeOf e
    in AppE1 t (Prim1 Transpose P.$ t .-> t) e

sum :: Expr -> Expr
sum e = let (ListT t) = typeOf e
         in if isNum t
                then AppE1 t (Prim1 Sum P.$ ListT t .-> t) e
                else tyErr "sum"

avg :: Expr -> Expr
avg e = let (ListT t) = typeOf e
         in if isNum t
                then AppE1 doubleT (Prim1 Avg P.$ ListT t .-> doubleT) e
                else tyErr "avg"

minimum :: Expr -> Expr
minimum e = let (ListT t) = typeOf e
             in if isNum t
                 then AppE1 t (Prim1 Minimum P.$ ListT t .-> t) e
                 else tyErr "minimum"

maximum :: Expr -> Expr
maximum e = let (ListT t) = typeOf e
             in if isNum t
                 then AppE1 t (Prim1 Maximum P.$ ListT t .-> t) e
                 else tyErr "maximum"

the :: Expr -> Expr
the e = let (ListT t) = typeOf e
         in AppE1 t (Prim1 The P.$ ListT t .-> t) e

head :: Expr -> Expr
head e = let (ListT t) = typeOf e
          in AppE1 t (Prim1 Head P.$ ListT t .-> t) e

last :: Expr -> Expr
last e = let (ListT t) = typeOf e
          in AppE1 t (Prim1 Last P.$ ListT t .-> t) e

tail :: Expr -> Expr
tail e = let (ListT t) = typeOf e
          in AppE1 (ListT t) (Prim1 Tail P.$ ListT t .-> ListT t) e

nub :: Expr -> Expr
nub e = let (ListT t) = typeOf e
         in AppE1 (ListT t) (Prim1 Nub P.$ ListT t .-> ListT t) e

number :: Expr -> Expr
number e = let (ListT t) = typeOf e
           in AppE1 (ListT (PairT t IntT )) (Prim1 Number P.$ ListT t .-> ListT (PairT t IntT )) e

guard :: Expr -> Expr
guard e = AppE1 (listT UnitT) (Prim1 Guard P.$ boolT .-> listT UnitT) e

init :: Expr -> Expr
init e = let (ListT t) = typeOf e
        in AppE1 (ListT t) (Prim1 Init P.$ ListT t .-> ListT t) e

fst :: Expr -> Expr
fst e = let t@(PairT t1 _) = typeOf e
         in AppE1 t1 (Prim1 Fst P.$ t .-> t1) e

snd :: Expr -> Expr
snd e = let t@(PairT _ t2) = typeOf e
         in AppE1 t2 (Prim1 Snd P.$ t .-> t2) e

map :: Expr -> Expr -> Expr
map f es = let ft@(FunT ta tr) = typeOf f
               te@(ListT t)    = typeOf es
            in if t P.== ta
                 then AppE2 (listT tr) (Prim2 Map P.$ ft .-> te .-> listT tr) f es
                 else tyErr "map"

concatMap :: Expr -> Expr -> Expr
concatMap f es = let ft@(FunT ta tr) = typeOf f
                     te@(ListT t)    = typeOf es
                  in if t P.== ta
                     then AppE2 tr (Prim2 ConcatMap (ft .-> (te .-> tr))) f es
                     else tyErr "concatMap"

filter :: Expr -> Expr -> Expr
filter f es = let ft@(FunT _ BoolT) = typeOf f
                  te@(ListT _) = typeOf es
               in AppE2 te (Prim2 Filter P.$ ft .-> te .-> te) f es

groupWithKey :: Expr -> Expr -> Expr
groupWithKey f es = let ft@(FunT ta tk) = typeOf f
                        te@(ListT t)   = typeOf es
                        tr            = listT P.$ pairT tk te
                    in if t P.== ta
                       then AppE2 tr (Prim2 GroupWithKey P.$ ft .-> te .-> tr) f es
                       else tyErr "groupWithKey"

sortWith :: Expr -> Expr -> Expr
sortWith f es = let ft@(FunT ta _) = typeOf f
                    te@(ListT t) = typeOf es
                 in if t P.== ta
                        then AppE2 te (Prim2 SortWith P.$ ft .-> te .-> te) f es
                        else tyErr "sortWith"

pair :: Expr -> Expr -> Expr
pair (Lit t1 v1) (Lit t2 v2) = Lit (pairT t1 t2) (L.PairV v1 v2)
pair e1 e2 = let t1 = typeOf e1
                 t2 = typeOf e2
              in AppE2 (pairT t1 t2) (Prim2 Pair P.$ t1 .-> t2 .-> pairT t1 t2) e1 e2

append :: Expr -> Expr -> Expr
append e1 e2 = let t1@(ListT _) = typeOf e1
                   t2@(ListT _) = typeOf e2
                in if t1 P.== t2
                    then AppE2 t1 (Prim2 Append P.$ t1 .-> t1 .-> t1) e1 e2
                    else tyErr "append"

index :: Expr -> Expr -> Expr
index e1 e2 = let t1@(ListT t) = typeOf e1
                  t2 = typeOf e2
                in if intT P.== t2
                    then AppE2 t (Prim2 Index P.$ t1 .-> t2 .-> t) e1 e2
                    else tyErr "index"



snoc :: Expr -> Expr -> Expr
snoc e1 e2 = let t1@(ListT t) = typeOf e1
              in if t P.== typeOf e2
                    then append e1 (cons e2 P.$ nil t1)
                    else tyErr "snoc"

cons :: Expr -> Expr -> Expr
cons e1 e2 = let t1 = typeOf e1
                 t@(ListT t2) = typeOf e2
              in if t1 P.== t2
                   then AppE2 t (Prim2 Cons (t1 .-> t .-> t)) e1 e2
                   else trace (pp e1) P.$ trace (pp e2) P.$ tyErrShow "cons" [t1, t2]

zip :: Expr -> Expr -> Expr
zip e1 e2 = let t1@(ListT t1') = typeOf e1
                t2@(ListT t2') = typeOf e2
             in AppE2 (listT P.$ pairT t1' t2') 
                      (Prim2 Zip P.$ t1 .-> t2 .-> listT (pairT t1' t2')) 
                      e1 
                      e2

var :: Type -> P.String -> Expr
var = Var

table :: Type -> P.String -> [L.Column] -> L.TableHints -> Expr
table = Table

lambda :: Type -> P.String -> Expr -> Expr
lambda = Lam

cond :: Expr -> Expr -> Expr -> Expr
cond eb et ee = let tb = typeOf eb
                    tt = typeOf et
                    te = typeOf ee
                 in if tb P.== boolT P.&& tt P.== te
                      then If te eb et ee
                      else tyErr "cond"

---------------------------------------------------------------------------------------
-- Smart constructors for join operators

cartproduct :: Expr -> Expr -> Expr
cartproduct xs ys = AppE2 resType (Prim2 CartProduct prodType) xs ys
  where
    resType  = listT P.$ pairT (elemT P.$ typeOf xs) (typeOf ys)
    prodType = typeOf xs .-> typeOf ys .-> resType

nestjoin :: Expr -> Expr -> L.JoinPredicate L.JoinExpr -> Expr
nestjoin xs ys p = AppE2 resType (Prim2 (NestJoin p) joinType) xs ys
  where
    resType  = listT P.$ pairT (elemT P.$ typeOf xs) (typeOf ys)
    joinType = typeOf xs .-> typeOf ys .-> resType

thetajoin :: Expr -> Expr -> L.JoinPredicate L.JoinExpr -> Expr
thetajoin xs ys p = AppE2 rt (Prim2 (ThetaJoin p) jt) xs ys
  where
    xst = typeOf xs
    yst = typeOf ys
    rt  = listT (pairT (elemT xst) (elemT yst))
    jt  = xst .-> yst .-> rt

semijoin :: Expr -> Expr -> L.JoinPredicate L.JoinExpr -> Expr
semijoin xs ys p = AppE2 xst (Prim2 (SemiJoin p) jt) xs ys
  where
    xst = typeOf xs
    yst = typeOf ys
    jt  = xst .-> yst .-> xst

antijoin :: Expr -> Expr -> L.JoinPredicate L.JoinExpr -> Expr
antijoin xs ys p = AppE2 xst (Prim2 (AntiJoin p) jt) xs ys
  where
    xst = typeOf xs
    yst = typeOf ys
    jt  = xst .-> yst .-> xst

---------------------------------------------------------------------------------------
-- Literal value constructors

unit :: Expr
unit = Lit unitT L.UnitV

int :: P.Int -> Expr
int i = Lit intT (L.IntV i)

bool :: P.Bool -> Expr
bool b = Lit boolT (L.BoolV b)

string :: P.String -> Expr
string s = Lit stringT (L.StringV s)

double :: P.Double -> Expr
double d = Lit doubleT (L.DoubleV d)

nil :: Type -> Expr
nil t = Lit t (L.ListV [])

list :: Type -> [Expr] -> Expr
list t es = toListT (nil t) es

consOpt :: Expr -> Expr -> Expr
consOpt e1 e2 = toListT e2 [e1]

toListT :: Expr -> [Expr] -> Expr
toListT n es = primList (P.reverse es) n
    where
        primList :: [Expr] -> Expr -> Expr
        primList ((Lit _ v):vs) (Lit ty (L.ListV xs)) = primList vs (Lit ty (L.ListV (v:xs)))
        primList [] e = e
        primList vs c@(Lit _ (L.ListV [])) = consList vs c
        primList vs e = consList vs e
        consList :: [Expr] -> Expr -> Expr
        consList xs e = P.foldl (P.flip cons) e xs

---------------------------------------------------------------------------------------
-- Smart constructors for scalar unary operators

scalarUnOp :: L.ScalarUnOp -> Expr -> Expr
scalarUnOp op e =
    let t = typeOf e
    in case (op, t) of
           (L.SUNumOp _, DoubleT)                 -> UnOp t op e
           (L.SUBoolOp _, BoolT)                  -> UnOp BoolT op e
           (L.SUCastOp L.CastDouble, _) | isNum t -> UnOp DoubleT op e
           (L.SUDateOp, _)                        -> $unimplemented
           (_, _)                                 -> P.error err
               where err = printf "CL.Primitives.scalarUnOp: %s" (P.show (op, t))

castDouble :: Expr -> Expr
castDouble = scalarUnOp (L.SUCastOp L.CastDouble)

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

---------------------------------------------------------------------------------------
-- Smart constructors for scalar binary operators

scalarBinOp :: L.ScalarBinOp -> Expr -> Expr -> Expr
scalarBinOp op e1 e2 =
    let t1 = typeOf e1
        t2 = typeOf e2
    in case (op, t1, t2) of
           (L.SBNumOp _, _, _) | t1 P.== t2 P.&& isNum t1 P.&& isNum t2 -> BinOp t1 op e1 e2
           (L.SBRelOp _, _, _) | t1 P.== t2                             -> BinOp BoolT op e1 e2
           (L.SBBoolOp _, BoolT, BoolT)                                 -> BinOp BoolT op e1 e2
           (L.SBStringOp L.Like, StringT, StringT)                      -> BinOp BoolT op e1 e2
           _                                                            -> P.error err
               where err = printf "CL.Primitives.scalarBinOp: %s" (P.show (op, t1, t2))

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
