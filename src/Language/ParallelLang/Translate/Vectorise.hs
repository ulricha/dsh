module Language.ParallelLang.Translate.Vectorise where

import Language.ParallelLang.FKL.Data.FKL
import qualified Language.ParallelLang.Common.Data.Type as T
import Language.ParallelLang.Common.Data.Type(Type, Typed, typeOf)
import Language.ParallelLang.VL.Data.VectorTypes
import Language.ParallelLang.Translate.TransM

import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Common.Data.Val


vectoriseType :: T.Type -> VType
vectoriseType (T.TyC s []) | isPrimTy s = pValT
                           | otherwise  = error $ "Primitive type not supported: " ++ show s
vectoriseType (T.TyC "List" [t@(T.TyC "List" _)])  = nVectorT' (vectoriseType t)
vectoriseType (T.TyC "List" [(T.TyC _ [])])      = valVT
vectoriseType (T.TyC s args) | isTuple s           = tupleT (map vectoriseType args)
vectoriseType (T.Fn t1 t2) = vectoriseType t1 .~> vectoriseType t2
vectoriseType t            = error $ "vectoriseType: Type not supported: " ++ show t

isPrimTy :: String -> Bool
isPrimTy = flip elem ["Int", "Bool", "Char"]

isTuple :: String -> Bool
isTuple ('(':xs) = let l = length xs
                  in (replicate (l - 1) ',' ++ ")") == xs
isTuple _      = False


-- | Vector primitive constructor functions

outer :: Expr VType -> Expr VType
outer e1 | nestingDepth (typeOf e1) > 0 = App descrT (Var (typeOf e1 .~> descrT) "outer" 0) [e1]
         | otherwise = error "Outer: Can't construct outer node"

distPrim :: Expr VType -> Expr VType -> Expr VType
distPrim e1 e2 | typeOf e1 == pValT && descrOrVal (typeOf e2)
                        = App valVT (Var (typeOf e1 .~> typeOf e2 .~> valVT) "distPrim" 0) [e1, e2]
               | otherwise = error "distPrim: Can't construct distPrim node"

distDesc :: Expr VType -> Expr VType -> Expr VType
distDesc e1 e2 | descrOrVal (typeOf e1) && descrOrVal (typeOf e2)
                        = let rt = tupleT [typeOf e1, propT]
                           in App rt (Var (typeOf e1 .~> typeOf e2 .~> rt) "distDesc" 0) [e1, e2]
                | otherwise = error "distDesc: Can't construct distDesc node"
                
distLift :: Expr VType -> Expr VType -> Expr VType
distLift e1 e2 | descrOrVal (typeOf e1) && descrOrVal (typeOf e2) 
                        = let rt = tupleT [typeOf e1, propT]
                           in App rt (Var (typeOf e1 .~> typeOf e2 .~> rt) "distLift" 0) [e1, e2]
               | otherwise = error "distLift: Can't construct distLift node"
               
propagateIn :: Expr VType -> Expr VType -> Expr VType
propagateIn e1 e2 | typeOf e1 == propT &&  descrOrVal (typeOf e2)
                        = let rt = tupleT [typeOf e1, propT]
                           in App rt (Var (typeOf e1 .~> typeOf e2 .~> rt) "propagateIn" 0) [e1, e2]
                  | otherwise = error "propagateIn: Can't construct propagateIn node"

rename :: Expr VType -> Expr VType -> Expr VType
rename e1 e2 | typeOf e1 == propT && descrOrVal (typeOf e2)
                        = App (typeOf e1) (Var (typeOf e1 .~> typeOf e2 .~> typeOf e1) "rename" 0) [e1, e2]
             | otherwise = error "rename: Can't construct rename node"

attach :: Expr VType -> Expr VType -> Expr VType
attach e1 e2 | typeOf e1 == descrT && nestingDepth (typeOf e2) > 0
                        = let rt = nVectorT' (typeOf e2)
                           in App rt (Var (typeOf e1 .~> typeOf e2 .~> rt) "attach" 0) [e1, e2]
             | otherwise = error "attach: Can't construct attach node"
             
singletonPrim :: Expr VType -> Expr VType
singletonPrim e1 | typeOf e1 == pValT = App valVT (Var (typeOf e1 .~> valVT) "singletonPrim" 0) [e1]
                 | otherwise = error "singletonPrim: Can't construct singletonPrim node"

singletonVec :: Expr VType -> Expr VType
singletonVec e1 | nestingDepth (typeOf e1) > 0
                    = let rt = nVectorT' (typeOf e1)
                       in App rt (Var (typeOf e1 .~> rt) "singletonVec" 0) [e1]
                | otherwise = error "singletonVec: Can't construct singletonVec node"

append :: Expr VType -> Expr VType -> Expr VType
append e1 e2 | descrOrVal (typeOf e1) && descrOrVal (typeOf e2) && typeOf e1 == typeOf e2
                    = let rt = tupleT [typeOf e1, propT, propT]
                       in App rt (Var (typeOf e1 .~> typeOf e2 .~> rt) "append" 0) [e1, e2]
             | otherwise = error "append: Can't construct append node"
             
segment :: Expr VType -> Expr VType
segment e1 | descrOrVal (typeOf e1) = App (typeOf e1) (Var (typeOf e1 .~> typeOf e1) "segment" 0) [e1]
           | otherwise = error "segment: Can't construct segment node"
           
restrictVec :: Expr VType -> Expr VType -> Expr VType
restrictVec e1 e2 | descrOrVal (typeOf e1) && nestingDepth (typeOf e2) == 1
                        = let rt = tupleT [typeOf e1, propT]
                           in App rt (Var (typeOf e1 .~> typeOf e2 .~> rt) "restrictVec" 0) [e1, e2]
                  | otherwise = error "restrictVec: Can't construct restrictVec node"
                           
combineVec :: Expr VType -> Expr VType -> Expr VType -> Expr VType
combineVec eb e1 e2 | nestingDepth (typeOf eb) == 1 && descrOrVal (typeOf e1) && descrOrVal (typeOf e2) && typeOf e1 == typeOf e2
                        = let rt = tupleT [typeOf e1, propT, propT]
                           in App rt (Var (typeOf eb .~> typeOf e1 .~> typeOf e2 .~> rt) "combineVec" 0) [eb, e1, e2]
                    | otherwise = error "combineVec: Can't construct combineVec node"
                    
bPermute :: Expr VType -> Expr VType -> Expr VType
bPermute e1 e2 | descrOrVal (typeOf e1) && nestingDepth (typeOf e2) == 1
                        = let rt = tupleT [typeOf e1, propT]
                           in App rt (Var (typeOf e1 .~> typeOf e2 .~> rt) "bPermute" 0) [e1, e2]
               | otherwise = error "bPermute: Can't construct bPermute node"

extract :: Expr VType -> Int -> Expr VType
extract e i | nestingDepth (typeOf e) > i && i > 0
                        = let rt = nVectorT (nestingDepth (typeOf e) - i)
                           in App rt (Var (typeOf e .~> pValT .~> rt) "extract" 0) [e, intV i]

intV :: Int -> Expr VType
intV i = Const pValT (Int i)
-- | Other construction functions

project :: Expr VType -> Int -> Expr VType
project e i = let t = typeOf e
                in case t of
                    (Tuple ts) -> if length ts >= i 
                                            then Proj (ts !! (i - 1)) 0 e i
                                            else error "Provided tuple expression is not big enough"
                    _                -> error "Provided type is not a tuple"

-- | Chain propagation
chainPropagate :: Expr VType -> Expr VType -> TransM (Expr VType)
chainPropagate pV rV | typeOf pV == propT && nestingDepth (typeOf rV) == 1
                        = return $ flip project 1 $ propagateIn pV rV
                    | typeOf pV == propT && nestingDepth (typeOf rV) > 1
                        = do
                            r <- getFreshVar
                            v <- getFreshVar
                            p <- getFreshVar
                            (b, d, vs) <- patV rV
                            let val = propagateIn pV d
                            let r' = Var (typeOf val) r 0
                            let valV = project r' 1
                            let v' = Var (typeOf valV) v 0
                            let valP = project r' 2
                            let p' = Var (typeOf valP) p 0
                            recurse <- chainPropagate p' vs
                            return $ b $ letF r val (letF v valV (letF p valP (attach v' recurse)))


patV :: Expr VType -> TransM (Expr VType -> Expr VType, Expr VType, Expr VType)
patV e | nestingDepth (typeOf e) > 1
                = do
                    hd <- getFreshVar
                    tl <- getFreshVar
                    v <- getFreshVar
                    let v' = Var (typeOf e) v 0
                    let hdv = outer v'
                    let tlv = extract v' 1
                    let hd' = Var (typeOf hdv) hd 0
                    let tl' = Var (typeOf tlv) tl 0
                    let e' = \x -> letF v e (letF hd hdv (letF tl tlv x))
                    return (e', hd', tl')
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