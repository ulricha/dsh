module Language.ParallelLang.Translate.Vectorise where

import Language.ParallelLang.FKL.Data.FKL
import qualified Language.ParallelLang.Common.Data.Type as T
import Language.ParallelLang.Common.Data.Type(Typed, typeOf)
import Language.ParallelLang.VL.Data.VectorTypes
import Language.ParallelLang.Translate.TransM

import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.VL.VectorPrimitives


vectoriseType :: T.Type -> VType
vectoriseType (T.TyC s [])   | isPrimTy s          = pValT
                             | otherwise           = error $ "Primitive type not supported: " ++ show s
vectoriseType (T.TyC "List" [t@(T.TyC "List" _)])  = nVectorT' (vectoriseType t)
vectoriseType (T.TyC "List" [(T.TyC _ [])])        = valVT
vectoriseType (T.TyC s args) | isTuple s           = tupleT (map vectoriseType args)
vectoriseType (T.Fn t1 t2)                         = vectoriseType t1 .~> vectoriseType t2
vectoriseType t                                    = error $ "vectoriseType: Type not supported: " ++ show t

isPrimTy :: String -> Bool
isPrimTy = flip elem ["Int", "Bool", "Char"]

isTuple :: String -> Bool
isTuple ('(':xs) = let l = length xs
                    in (replicate (l - 1) ',' ++ ")") == xs
isTuple _        = False




{-
App   :: Type -> Expr -> [Expr] -> Expr -- | Apply multiple arguments to an expression
Fn    :: Type -> String -> Int -> [String] -> Expr -> Expr -- | A function has a name (and lifted level), some arguments and a body
Let   :: Type -> String -> Expr -> Expr -> Expr -- | Let a variable have value expr1 in expr2
If    :: Type -> Expr -> Expr -> Expr -> Expr -- | If expr1 then expr2 else expr3
BinOp :: Type -> Op -> Expr -> Expr -> Expr -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
Const :: Type -> Val -> Expr -- | Constant value
Var   :: Type -> String -> Int -> Expr  -- | Variable lifted to level i
Nil   :: Type -> Expr -- | []
Proj  :: Type -> Int -> Expr -> Int -> Expr
-}