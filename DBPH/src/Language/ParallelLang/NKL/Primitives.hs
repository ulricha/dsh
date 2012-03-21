module Language.ParallelLang.NKL.Primitives where
    
import qualified Prelude as P

import Language.ParallelLang.NKL.Data.NKL
import Language.ParallelLang.Common.Data.Type(splitType, intT, boolT, isListT, (.->), listDepth, unliftType, Type(..), isNum)
import qualified Language.ParallelLang.Common.Data.Type as T

($) :: Expr -> Expr -> Expr
f $ e = let tf = typeOf f
            te = typeOf e
            (ta, tr) = splitType tf
         in if ta P.== te 
              then App tr f e
              else P.error P.$ "NKLPrims.($): Cannot apply a function that expects: " P.++ P.show ta P.++ " to an argument of type: " P.++ P.show te

length :: Expr -> Expr
length e = let t = typeOf e
            in if isListT t 
                 then AppE1 intT (Length P.$ t .-> intT) e
                 else P.error P.$ "NKLPrims.length: Cannot apply length to an argument of type: " P.++ P.show t
                 
not :: Expr -> Expr 
not e = let t = typeOf e
         in if boolT P.== t
                then AppE1 boolT (Length P.$ t .-> t) e
                else P.error P.$ "NKLPrims.not: Cannot apply not to an argument of type: " P.++ P.show t

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
                
the :: Expr -> Expr
the e = let (List t) = typeOf e
         in AppE1 t (The P.$ List t .-> t) e
         
fst :: Expr -> Expr
fst e = let t@(T.Pair t1 _) = typeOf e
         in AppE1 t1 (Fst P.$ t .-> t1) e
         
snd :: Expr -> Expr
snd e = let t@(T.Pair _ t2) = typeOf e
         in AppE1 t2 (Snd P.$ t .-> t2) e

{-
     
data Expr where
    Table :: Type -> String -> [Column] -> [Key] -> Expr
    AppE2 :: Type -> Prim2 -> Expr -> Expr -> Expr 
    BinOp :: Type -> Op -> Expr -> Expr -> Expr -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
    Lam   :: Type -> String -> Expr -> Expr -- | A function has a name, some arguments and a body
    Let   :: Type -> String -> Expr -> Expr -> Expr -- | Let a variable have value expr1 in expr2
    If    :: Type -> Expr -> Expr -> Expr -> Expr -- | If expr1 then expr2 else expr3
    Const :: Type -> Val -> Expr -- | Constant value
    Var   :: Type -> String -> Expr  -- | Variable
      deriving (Show, Eq, Ord)



data Prim2 = Map Type
           | GroupWith Type
           | SortWith Type
           | Pair Type
    deriving (Show, Eq, Ord)
-}