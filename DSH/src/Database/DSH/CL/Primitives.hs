-- | Smart constructors for CL primitives
module Database.DSH.CL.Primitives where
       
import Debug.Trace
    
import qualified Prelude as P
import           Prelude (Bool(..))

import           Text.Printf

import           Database.DSH.CL.Lang
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Data.Type
import           Database.DSH.Common.Data.Op
import qualified Database.DSH.Common.Data.Val as V

($) :: Expr -> Expr -> Expr
f $ e = let tf = typeOf f
            te = typeOf e
            (ta, tr) = splitType tf
         in if ta P.== te
              then App tr f e
              else P.error P.$ "NKLPrims.($): Cannot apply a function that expects: " P.++ P.show ta P.++ " to an argument of type: " P.++ P.show te

reverse :: Expr -> Expr
reverse e = let t@(ListT _) = typeOf e
             in AppE1 t (Prim1 Reverse P.$ t .-> t) e

length :: Expr -> Expr
length e = let t = typeOf e
            in if isList t
                 then AppE1 intT (Prim1 Length P.$ t .-> intT) e
                 else P.error P.$ "NKLPrims.length: Cannot apply length to an argument of type: " P.++ P.show t P.++
                                  "\nThe provided argument is: " P.++ P.show e


unzip :: Expr -> Expr
unzip e = let (ListT (PairT t1 t2)) = typeOf e
              left  = map (lambda (PairT t1 t2 .-> t1) "__*unzl*" (fst (var (PairT t1 t2) "__*unzl*"))) e
              right = map (lambda (PairT t1 t2 .-> t2) "__*unzr*" (snd (var (PairT t1 t2) "__*unzr*"))) e
           in pair left right
                 
all :: Expr -> Expr -> Expr
all f e = and (map f e)

any :: Expr -> Expr -> Expr
any f e = or (map f e)

null :: Expr -> Expr
null e = length e `eq` int 0

and :: Expr -> Expr
and e = let t = typeOf e
         in if listT boolT P.== t
                then AppE1 boolT (Prim1 And P.$ t .-> boolT) e
                else P.error P.$ "NKLPrims.and: Cannot apply and to an argument of type: " P.++ P.show t

or :: Expr -> Expr
or e = let t = typeOf e
         in if listT boolT P.== t
                then AppE1 boolT (Prim1 Or P.$ t .-> boolT) e
                else P.error P.$ "NKLPrims.or: Cannot apply or to an argument of type: " P.++ P.show t

concat :: Expr -> Expr
concat e = let t = typeOf e
            in if listDepth t P.> 1
                    then AppE1 (unliftType t) (Prim1 Concat P.$ t .-> unliftType t) e
                    else P.error P.$ "NKLPrims.concat: Cannot apply concat to an argument of type: " P.++ P.show t

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
                else P.error P.$ "NKLPrims.sum: Cannot apply sum to an argument of type: " P.++ P.show (ListT t)

avg :: Expr -> Expr
avg e = let (ListT t) = typeOf e
         in if isNum t
                then AppE1 t (Prim1 Avg P.$ ListT t .-> t) e
                else P.error P.$ "NKLPrims.avg: Cannot apply avg to an argument of type: " P.++ P.show (ListT t)

minimum :: Expr -> Expr
minimum e = let (ListT t) = typeOf e
             in if isNum t
                 then AppE1 t (Prim1 Minimum P.$ ListT t .-> t) e
                 else P.error P.$ "NKLPrims.minimum: Cannot apply sum to an argument of type: " P.++ P.show (ListT t)

maximum :: Expr -> Expr
maximum e = let (ListT t) = typeOf e
             in if isNum t
                 then AppE1 t (Prim1 Maximum P.$ ListT t .-> t) e
                 else P.error P.$ "NKLPrims.maximum: Cannot apply sum to an argument of type: " P.++ P.show (ListT t)

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
                 else P.error P.$ "NKLPrims.map: Cannot apply map to a function of type: \n" 
                                  P.++ P.show ft 
                                  P.++ "\n and an argument of type: \n" 
                                  P.++ P.show te
                                  P.++ "\n"
                                  P.++ P.show f
                                  
concatMap :: Expr -> Expr -> Expr
concatMap f es = let ft@(FunT ta tr) = typeOf f
                     te@(ListT t)    = typeOf es
                  in if t P.== ta
                     then AppE2 tr (Prim2 ConcatMap (ft .-> (te .-> tr))) f es
                     else P.error "concatMap type error"

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
                       else P.error P.$ "NKLPrims.groupWithKey: Cannot apply groupWithKey to a function of type: " P.++ P.show ft P.++ " and an argument of type: " P.++ P.show te

sortWith :: Expr -> Expr -> Expr
sortWith f es = let ft@(FunT ta _) = typeOf f
                    te@(ListT t) = typeOf es
                 in if t P.== ta
                        then AppE2 te (Prim2 SortWith P.$ ft .-> te .-> te) f es
                        else P.error P.$ "NKLPrims.sortWith: Cannot apply sortWith to a function of type: " P.++ P.show ft P.++ " and an argument of type: " P.++ P.show te

pair :: Expr -> Expr -> Expr
pair (Lit t1 v1) (Lit t2 v2) = Lit (pairT t1 t2) (V.PairV v1 v2)
pair e1 e2 = let t1 = typeOf e1
                 t2 = typeOf e2
              in AppE2 (pairT t1 t2) (Prim2 Pair P.$ t1 .-> t2 .-> pairT t1 t2) e1 e2

append :: Expr -> Expr -> Expr
append e1 e2 = let t1@(ListT _) = typeOf e1
                   t2@(ListT _) = typeOf e2
                in if t1 P.== t2
                    then AppE2 t1 (Prim2 Append P.$ t1 .-> t1 .-> t1) e1 e2
                    else P.error P.$ "NKLPrims.append: Cannot append two list with different types"

index :: Expr -> Expr -> Expr
index e1 e2 = let t1@(ListT t) = typeOf e1
                  t2 = typeOf e2
                in if intT P.== t2
                    then AppE2 t (Prim2 Index P.$ t1 .-> t2 .-> t) e1 e2
                    else P.error P.$ "NKLPrims.index: Cannot perform index with given arguments."

scalarUnOp :: ScalarUnOp -> Expr -> Expr
scalarUnOp op e =
    let t = typeOf e
    in case (op, t) of
           (Not, BoolT)       -> UnOp t op e
           (CastDouble, IntT) -> UnOp t op e
           (Sin, DoubleT)     -> UnOp t op e
           (Cos, DoubleT)     -> UnOp t op e
           (Tan, DoubleT)     -> UnOp t op e
           (Sqrt, DoubleT)    -> UnOp t op e
           (Log, DoubleT)     -> UnOp t op e
           (Exp, DoubleT)     -> UnOp t op e
           (ASin, DoubleT)    -> UnOp t op e
           (ACos, DoubleT)    -> UnOp t op e
           (ATan, DoubleT)    -> UnOp t op e
           (_, _)             -> P.error P.$ printf "Primitives.scalarUnOp: %s" (P.show (op, t))

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
             in if t1 P.== intT P.&& t2 P.== intT
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
                   
like :: Expr -> Expr -> Expr
like e1 e2 = let t1 = typeOf e1
                 t2 = typeOf e2
             in if t1 P.== stringT P.&& t2 P.== stringT
                then BinOp boolT Like e1 e2
                else P.error P.$ "NKLPrims.like: Cannot apply like to arguments of type: "P.++ P.show t1 P.++ " and " P.++ P.show t2

snoc :: Expr -> Expr -> Expr
snoc e1 e2 = let t1@(ListT t) = typeOf e1
              in if t P.== typeOf e2
                    then append e1 (cons e2 P.$ nil t1)
                    else P.error P.$ "NKLPrims.snoc: Cannot apply snoc to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show (typeOf e2)

cons :: Expr -> Expr -> Expr
cons e1 e2 = let t1 = typeOf e1
                 t@(ListT t2) = typeOf e2
              in if t1 P.== t2
                   then AppE2 t (Prim2 Cons (t1 .-> t .-> t)) e1 e2
                   else P.error P.$ "NKLPrims.cons: Cannot apply cons to arguments of type : " P.++ P.show t1 P.++ " and: " P.++ P.show t2

max :: Expr -> Expr -> Expr
max e1 e2 = cond (e1 `gt` e2) e1 e2

min :: Expr -> Expr -> Expr
min e1 e2 = cond (e1 `gt` e2) e2 e1

zip :: Expr -> Expr -> Expr
zip e1 e2 = let t1@(ListT t1') = typeOf e1
                t2@(ListT t2') = typeOf e2
             in AppE2 (listT P.$ pairT t1' t2') (Prim2 Zip P.$ t1 .-> t2 .-> listT (pairT t1' t2')) e1 e2

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
                      
nestjoin :: Expr -> Expr -> JoinExpr -> JoinExpr -> Expr
nestjoin xs ys p1 p2 = AppE2 resType (Prim2 (NestJoin p1 p2) joinType) xs ys
  where
    resType  = listT P.$ pairT (elemT P.$ typeOf xs) (typeOf ys)
    joinType = typeOf xs .-> typeOf ys .-> resType
    
equijoin :: Expr -> Expr -> JoinExpr -> JoinExpr -> Expr
equijoin xs ys p1 p2 = AppE2 rt (Prim2 (EquiJoin p1 p2) jt) xs ys
  where
    xst = typeOf xs
    yst = typeOf ys
    rt  = pairT (elemT xst) (elemT yst)
    jt  = xst .-> yst .-> rt

semijoin :: Expr -> Expr -> JoinExpr -> JoinExpr -> Expr
semijoin xs ys p1 p2 = AppE2 xst (Prim2 (SemiJoin p1 p2) jt) xs ys
  where
    xst = typeOf xs
    yst = typeOf ys
    jt  = xst .-> yst .-> xst
    
antijoin :: Expr -> Expr -> JoinExpr -> JoinExpr -> Expr
antijoin xs ys p1 p2 = AppE2 xst (Prim2 (AntiJoin p1 p2) jt) xs ys
  where
    xst = typeOf xs
    yst = typeOf ys
    jt  = xst .-> yst .-> xst

unit :: Expr
unit = Lit unitT V.UnitV

int :: P.Int -> Expr
int i = Lit intT (V.IntV i)

bool :: P.Bool -> Expr
bool b = Lit boolT (V.BoolV b)

string :: P.String -> Expr
string s = Lit stringT (V.StringV s)

double :: P.Double -> Expr
double d = Lit doubleT (V.DoubleV d)

nil :: Type -> Expr
nil t = Lit t (V.ListV [])

list :: Type -> [Expr] -> Expr
list t es = toListT (nil t) es

consOpt :: Expr -> Expr -> Expr
consOpt e1 e2 = toListT e2 [e1]
        
toListT :: Expr -> [Expr] -> Expr
toListT n es = primList (P.reverse es) n
    where
        primList :: [Expr] -> Expr -> Expr
        primList ((Lit _ v):vs) (Lit ty (V.ListV xs)) = primList vs (Lit ty (V.ListV (v:xs)))
        primList [] e = e
        primList vs c@(Lit _ (V.ListV [])) = consList vs c
        primList vs e = consList vs e
        consList :: [Expr] -> Expr -> Expr
        consList xs e = P.foldl (P.flip cons) e xs
