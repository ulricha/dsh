module Language.ParallelLang.NKL.NKLPrimitives (Expr, ($), filter, all, any, integerToDouble, and, or, reverse, unzip, length, not, concat, sum, the, minimum, maximum, head, tail, fst, snd, map, groupWith, sortWith, pair, add, sub, div, mul, mod, eq, gt, lt, gte, lte, conj, disj, cons, var, table, lambda, cond, unit, int, bool, string, double, nil, list, consOpt)where
    
import qualified Prelude as P
import Prelude (Bool(..))

import Language.ParallelLang.NKL.Data.NKL
import Language.ParallelLang.Common.Data.Type(unitT, splitType, intT, boolT, listT, stringT, doubleT, pairT, isListT, (.->), listDepth, unliftType, Type(List, Fn), isNum)
import qualified Language.ParallelLang.Common.Data.Type as T
import Language.ParallelLang.Common.Data.Op
import qualified Language.ParallelLang.Common.Data.Val as V

($) :: Expr -> Expr -> Expr
f $ e = let tf = typeOf f
            te = typeOf e
            (ta, tr) = splitType tf
         in if ta P.== te 
              then App tr f e
              else P.error P.$ "NKLPrims.($): Cannot apply a function that expects: " P.++ P.show ta P.++ " to an argument of type: " P.++ P.show te

reverse :: Expr -> Expr
reverse e = let t@(T.List _) = typeOf e
             in AppE1 t (Reverse P.$ t .-> t) e

length :: Expr -> Expr
length e = let t = typeOf e
            in if isListT t 
                 then AppE1 intT (Length P.$ t .-> intT) e
                 else P.error P.$ "NKLPrims.length: Cannot apply length to an argument of type: " P.++ P.show t

unzip :: Expr -> Expr
unzip e = let (T.List (T.Pair t1 t2)) = typeOf e
              left  = map (lambda (T.Pair t1 t2 .-> t1) "__*unzl*" (fst (var (T.Pair t1 t2) "__*unzl*"))) e
              right = map (lambda (T.Pair t1 t2 .-> t2) "__*unzr*" (snd (var (T.Pair t1 t2) "__*unzr*"))) e
           in pair left right
                 
not :: Expr -> Expr 
not e = let t = typeOf e
         in if boolT P.== t
                then AppE1 boolT (Not P.$ t .-> t) e
                else P.error P.$ "NKLPrims.not: Cannot apply not to an argument of type: " P.++ P.show t

all :: Expr -> Expr -> Expr
all f e = and (map f e)

any :: Expr -> Expr -> Expr
any f e = or (map f e)

and :: Expr -> Expr 
and e = let t = typeOf e
         in if listT boolT P.== t
                then AppE1 boolT (And P.$ t .-> boolT) e
                else P.error P.$ "NKLPrims.and: Cannot apply and to an argument of type: " P.++ P.show t

or :: Expr -> Expr 
or e = let t = typeOf e
         in if listT boolT P.== t
                then AppE1 boolT (Or P.$ t .-> boolT) e
                else P.error P.$ "NKLPrims.or: Cannot apply or to an argument of type: " P.++ P.show t

integerToDouble :: Expr -> Expr 
integerToDouble e = let t = typeOf e
                     in if intT P.== t
                         then AppE1 doubleT (IntegerToDouble P.$ t .-> doubleT) e
                         else P.error P.$ "NKLPrims.integerToDouble: Cannot apply integerToDouble to an argument of type: " P.++ P.show t

concat :: Expr -> Expr
concat e = let t = typeOf e
            in if listDepth t P.> 1
                    then AppE1 (unliftType t) (Concat P.$ t .-> unliftType t) e
                    else P.error P.$ "NKLPrims.concat: Cannot apply concat to an argument of type: " P.++ P.show t

sum :: Expr -> Expr
sum e = let (List t) = typeOf e
         in if isNum t
                then AppE1 t (Sum P.$ List t .-> t) e
                else P.error P.$ "NKLPrims.sum: Cannot apply sum to an argument of type: " P.++ P.show (List t)

minimum :: Expr -> Expr
minimum e = let (List t) = typeOf e
             in if isNum t
                 then AppE1 t (Minimum P.$ List t .-> t) e
                 else P.error P.$ "NKLPrims.minimum: Cannot apply sum to an argument of type: " P.++ P.show (List t)

maximum :: Expr -> Expr
maximum e = let (List t) = typeOf e
             in if isNum t
                 then AppE1 t (Maximum P.$ List t .-> t) e
                 else P.error P.$ "NKLPrims.maximum: Cannot apply sum to an argument of type: " P.++ P.show (List t)

the :: Expr -> Expr
the e = let (List t) = typeOf e
         in AppE1 t (The P.$ List t .-> t) e

head :: Expr -> Expr
head e = let (List t) = typeOf e
          in AppE1 t (Head P.$ List t .-> t) e

tail :: Expr -> Expr
tail e = let (List t) = typeOf e
          in AppE1 t (Tail P.$ List t .-> List t) e
         
fst :: Expr -> Expr
fst e = let t@(T.Pair t1 _) = typeOf e
         in AppE1 t1 (Fst P.$ t .-> t1) e
         
snd :: Expr -> Expr
snd e = let t@(T.Pair _ t2) = typeOf e
         in AppE1 t2 (Snd P.$ t .-> t2) e

map :: Expr -> Expr -> Expr
map f es = let ft@(Fn ta tr) = typeOf f
               te@(List t) = typeOf es
            in if t P.== ta
                 then AppE2 (listT tr) (Map P.$ ft .-> te .-> listT tr) f es
                 else P.error P.$ "NKLPrims.map: Cannot apply map to a function of type: " P.++ P.show ft P.++ " and an argument of type: " P.++ P.show te

filter :: Expr -> Expr -> Expr
filter f es = let ft@(Fn _ T.Bool) = typeOf f
                  te@(List _) = typeOf es
               in AppE2 te (Filter P.$ ft .-> te .-> te) f es

groupWith :: Expr -> Expr -> Expr
groupWith f es = let ft@(Fn ta _) = typeOf f
                     te@(List t) = typeOf es
                  in if t P.== ta
                       then AppE2 (listT te) (GroupWith P.$ ft .-> te .-> listT te) f es
                       else P.error P.$ "NKLPrims.groupWith: Cannot apply groupWith to a function of type: " P.++ P.show ft P.++ " and an argument of type: " P.++ P.show te

sortWith :: Expr -> Expr -> Expr
sortWith f es = let ft@(Fn ta _) = typeOf f
                    te@(List t) = typeOf es
                 in if t P.== ta
                        then AppE2 te (SortWith P.$ ft .-> te .-> te) f es
                        else P.error P.$ "NKLPrims.sortWith: Cannot apply sortWith to a function of type: " P.++ P.show ft P.++ " and an argument of type: " P.++ P.show te

pair :: Expr -> Expr -> Expr
pair (Const t1 v1) (Const t2 v2) = Const (pairT t1 t2) (V.Pair v1 v2)
pair e1 e2 = let t1 = typeOf e1
                 t2 = typeOf e2
              in AppE2 (pairT t1 t2) (Pair P.$ t1 .-> t2 .-> pairT t1 t2) e1 e2

add :: Expr -> Expr -> Expr
add e1 e2 = let t1 = typeOf e1
                t2 = typeOf e2
             in if isNum t1 P.&& t1 P.== t2
                 then BinOp t1 Add e1 e2
                 else P.error P.$ "NKLPrims.add: Cannot apply add to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

sub :: Expr -> Expr -> Expr
sub e1 e2 = let t1 = typeOf e1
                t2 = typeOf e2
             in if isNum t1 P.&& t1 P.== t2
                  then BinOp t1 Sub e1 e2
                  else P.error P.$ "NKLPrims.sub: Cannot apply sub to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

div :: Expr -> Expr -> Expr
div e1 e2 = let t1 = typeOf e1
                t2 = typeOf e2
             in if isNum t1 P.&& t1 P.== t2
                  then BinOp t1 Div e1 e2
                  else P.error P.$ "NKLPrims.div: Cannot apply div to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

mul :: Expr -> Expr -> Expr
mul e1 e2 = let t1 = typeOf e1
                t2 = typeOf e2
             in if isNum t1 P.&& t1 P.== t2
                  then BinOp t1 Mul e1 e2
                  else P.error P.$ "NKLPrims.mul: Cannot apply mul to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

mod :: Expr -> Expr -> Expr
mod e1 e2 = let t1 = typeOf e1
                t2 = typeOf e2
             in if isNum t1 P.&& t1 P.== t2
                  then BinOp t1 Mod e1 e2
                  else P.error P.$ "NKLPrims.mod: Cannot apply mod to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

eq :: Expr -> Expr -> Expr
eq e1 e2 = let t1 = typeOf e1
               t2 = typeOf e2
            in if t1 P.== t2
                 then BinOp boolT Eq e1 e2
                 else P.error P.$ "NKLPrims.eq: Cannot apply eq to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

gt :: Expr -> Expr -> Expr
gt e1 e2 = let t1 = typeOf e1
               t2 = typeOf e2
            in if t1 P.== t2
                 then BinOp boolT Gt e1 e2
                 else P.error P.$ "NKLPrims.gt: Cannot apply gt to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

lt :: Expr -> Expr -> Expr
lt e1 e2 = let t1 = typeOf e1
               t2 = typeOf e2
            in if t1 P.== t2
                 then BinOp boolT Lt e1 e2
                 else P.error P.$ "NKLPrims.lt: Cannot apply lt to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

gte :: Expr -> Expr -> Expr
gte e1 e2 = let t1 = typeOf e1
                t2 = typeOf e2
             in if t1 P.== t2
                  then BinOp boolT GtE e1 e2
                  else P.error P.$ "NKLPrims.gte: Cannot apply gte to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

lte :: Expr -> Expr -> Expr
lte e1 e2 = let t1 = typeOf e1
                t2 = typeOf e2
             in if t1 P.== t2
                  then BinOp boolT LtE e1 e2
                  else P.error P.$ "NKLPrims.lte: Cannot apply lte to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

conj :: Expr -> Expr -> Expr
conj e1 e2 = let t1 = typeOf e1
                 t2 = typeOf e2
              in if t1 P.== boolT P.&& t1 P.== t2
                   then BinOp boolT Conj e1 e2
                   else P.error P.$ "NKLPrims.conj: Cannot apply conj to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

disj :: Expr -> Expr -> Expr
disj e1 e2 = let t1 = typeOf e1
                 t2 = typeOf e2
              in if t1 P.== boolT P.&& t1 P.== t2
                   then BinOp boolT Disj e1 e2
                   else P.error P.$ "NKLPrims.disj: Cannot apply disj to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

cons :: Expr -> Expr -> Expr
cons e1 e2 = let t1 = typeOf e1
                 t@(List t2) = typeOf e2
              in if t1 P.== t2
                   then BinOp t Cons e1 e2
                   else P.error P.$ "NKLPrims.cons: Cannot apply cons to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

var :: Type -> P.String -> Expr
var = Var

table :: Type -> P.String -> [Column] -> [Key] -> Expr
table = Table

lambda :: Type -> P.String -> Expr -> Expr
lambda = Lam

cond :: Expr -> Expr -> Expr -> Expr
cond eb et ee = let tb = typeOf eb
                    tt = typeOf et
                    te = typeOf ee
                 in if tb P.== boolT P.&& tt P.== te
                      then If te eb et ee
                      else P.error P.$ "NKLPrims.cond: Cannot apply cond to arguments of type : " P.++ P.show tb P.++ ", " P.++ P.show tt P.++ " and: " P.++ P.show te

unit :: Expr
unit = Const unitT V.Unit

int :: P.Int -> Expr
int i = Const intT (V.Int i)

bool :: P.Bool -> Expr
bool b = Const boolT (V.Bool b)

string :: P.String -> Expr
string s = Const stringT (V.String s)

double :: P.Double -> Expr
double d = Const doubleT (V.Double d)

nil :: Type -> Expr
nil t = Const t (V.List []) 

list :: Type -> [Expr] -> Expr
list t es = toList (nil t) es

consOpt :: Expr -> Expr -> Expr
consOpt e1 e2 = toList e2 [e1]

toList :: Expr -> [Expr] -> Expr
toList n es = primList (P.reverse es) n 
    where
        primList :: [Expr] -> Expr -> Expr
        primList ((Const _ v):vs) (Const ty (V.List xs)) = primList vs (Const ty (V.List (v:xs)))
        primList [] e = e
        primList vs c@(Const _ (V.List [])) = consList vs c
        primList vs e = consList vs e
        consList :: [Expr] -> Expr -> Expr
        consList xs e = P.foldl (P.flip cons) e xs