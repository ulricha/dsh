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

-- * Translation smart constructors

dist :: Expr VType -> Expr VType -> TransM (Expr VType)
dist e1 e2 | typeOf e1 == pValT && nestingDepth (typeOf e2) > 0
                  -- Corresponds to rule [dist-1]
                = return $ distPrim e1 (outer e2)
            
            | nestingDepth (typeOf e1) == 1 && nestingDepth (typeOf e2) > 0
                  -- Corresponds to rule [dist-2]
                = return $ project (distDesc e1 (outer e2)) 1
            
            | nestingDepth (typeOf e1) > 1 && nestingDepth (typeOf e2) > 0
                  -- Corresponds to rule [dist-3]
                = do
                    -- Fresh variable names
                    h2 <- getFreshVar -- Variable for containing outer vector of e2
                    r  <- getFreshVar -- placeholder for distDesc e1 (outer e2)
                    d  <- getFreshVar 
                    p  <- getFreshVar
                    
                    let h2v = outer e2
                    let h2' = Var (typeOf h2v) h2 0
                    
                    (b1, h1, vs1) <- patV e1     -- Pattern match on vector structure of e1 (b1 contains the bindings)
                    let b2 = \x -> b1 (letF h2 h2v x) -- Add The declaration of h2 to the AST
                    
                    -- Construct (distDesc h1 h2) and a place holder variable
                    let rv = distDesc h1 h2'
                    let r' = Var (typeOf rv) r 0
                    
                    -- Do pattern matching r' extract d and p from it.
                    let dv = project r' 1
                    let d' = Var (typeOf dv) d 0
                    let pv = project r' 2
                    let p' = Var (typeOf pv) p 0
                    
                    -- Recursively propagate the new names through the inner vectors of e1
                    e3 <- chainPropagate p' vs1
                    
                    -- Glue together all variables with let bindings 
                    return (b2 (letF r rv (letF d dv (letF p pv (attach h2' (attach d' e3))))))
            | otherwise = error "dist: Can't construct dist node"  
            
distL :: Expr VType -> Expr VType -> TransM (Expr VType)
distL e1 e2 | nestingDepth (typeOf e1) == 1 && nestingDepth (typeOf e2) > 1
                -- Corresponds to rule [dist-lift]
                = do
                    (b, d2, vs2) <- patV e2 -- Pattern matching on e2: <d2, vs2> = e2
                    return $ b $ attach d2 $ project (distLift e1 (outer vs2)) 1
            
            | nestingDepth (typeOf e1) > 1 && nestingDepth (typeOf e2) > 1
                -- Corresponds to rule [dist-lift2]
                = do
                    (b1, d1, vs1) <- patV e1 -- Pattern matching on e1: <d1, vs1> = e1
                    (b2, d2, vs2) <- patV e2 -- Pattern mathcing on e2: <d2, vs2> = e2
                    
                    r <- getFreshVar -- Placeholder for distLift d1 (outer vs2)
                    d <- getFreshVar 
                    p <- getFreshVar
                    
                    let rv = distLift d1 (outer vs2)
                    let r' = Var (typeOf rv) r 0
                    
                    let dv = project r' 1
                    let d' = Var (typeOf dv) d 0
                    
                    let pv = project r' 2
                    let p' = Var (typeOf pv) p 0
                    
                    let b3 = \x -> letF r rv (letF d dv (letF p pv x))
                    
                    e3 <- chainPropagate p' vs1 -- recursively propagate changes through the inner vectors of e1
                    
                    return $ b1 (b2 (b3 (attach d2 (attach d' e3))))
            | otherwise = error "distL: Can't construct distL node"
                    
consEmpty :: Expr VType -> TransM (Expr VType)
consEmpty e | typeOf e == pValT 
                -- Corresponds to rule [cons-empty-1]
                = singletonPrim e
            
            | nestingDepth (typeOf e) > 0
                -- Corresponds to rule [cons-empty-2]
                = singletonVec e
            | otherwise = error "consEmpty: Can't construct consEmpty node"
            
cons :: Expr VType -> Expr VType -> TransM (Expr VType)
cons e1 e2 | typeOf e1 = pValT && nestingDepth (typeOf e2) == 1
                -- corresponds to rule [cons-1]
                = project (append (singletonPrim e1) e2) 1
            
            | nestingDepth (typeOf e1) > 0 && nestingDepth (typeOf e2) == (nestingDepth (typeOf e1)) + 1
                -- Corresponds to rule [cons-2]
                = do
                    e1a <- getFreshVar -- Variable to act as place holder for e1
                    r   <- getFreshVar -- Placeholder for append (outer $ singletonVec e1') d2
                    v   <- getFreshVar 
                    p1  <- getFreshVar
                    p2  <- getFreshVar
                    
                    let e1' = Var (typeOf e1) e1a 0 -- Construct the actual placeholder variable for e1
                    
                    (b1, d1, vs1) <- patV e1'  -- Pattern matching on e1': <d1, vs1> = e1'
                    (b2, d2, vs2) <- patV e2   -- Pattern matching on e2: <d2, vs2> = e2
                    
                     
                    
 
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