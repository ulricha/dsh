module Language.ParallelLang.Translate.Vectorise (runVectorise) where

import Language.ParallelLang.FKL.Data.FKL
import qualified Language.ParallelLang.Common.Data.Type as T
import Language.ParallelLang.Common.Data.Type(Typed, typeOf)
import Language.ParallelLang.VL.Data.VectorTypes
import Language.ParallelLang.Translate.TransM

import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.VL.VectorPrimitives

import Language.ParallelLang.FKL.Render.Render ()

import Control.Applicative ((<$>), (<*>))

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
                = do
                    d2 <- getFreshVar
                    let d2v = outer e2
                    let d2' = Var (typeOf d2v) d2
                    return $ letF d2 d2v $ attach d2' $ project (distDesc e1 d2') 1
            
            | nestingDepth (typeOf e1) > 1 && nestingDepth (typeOf e2) > 0
                  -- Corresponds to rule [dist-3]
                = do
                    
                    -- Fresh variable names
                    h2 <- getFreshVar -- Variable for containing outer vector of e2
                    r  <- getFreshVar -- placeholder for distDesc e1 (outer e2)
                    d  <- getFreshVar 
                    p  <- getFreshVar
                    
                    let h2v = outer e2
                    let h2' = Var (typeOf h2v) h2
                    
                    (b1, h1, vs1) <- patV e1     -- Pattern match on vector structure of e1 (b1 contains the bindings)
                    let b2 = \x -> b1 (letF h2 h2v x) -- Add The declaration of h2 to the AST
                    
                    -- Construct (distDesc h1 h2) and a place holder variable
                    let rv = distDesc h1 h2'
                    let r' = Var (typeOf rv) r
                    
                    -- Do pattern matching r' extract d and p from it.
                    let dv = project r' 1
                    let d' = Var (typeOf dv) d
                    let pv = project r' 2
                    let p' = Var (typeOf pv) p
                    
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
                    let r' = Var (typeOf rv) r
                    
                    let dv = project r' 1
                    let d' = Var (typeOf dv) d
                    
                    let pv = project r' 2
                    let p' = Var (typeOf pv) p
                    
                    let b3 = \x -> letF r rv (letF d dv (letF p pv x))
                    
                    e3 <- chainPropagate p' vs1 -- recursively propagate changes through the inner vectors of e1
                    
                    return $ b1 (b2 (b3 (attach d2 (attach d' e3))))
            | otherwise = error "distL: Can't construct distL node"
                    
consEmpty :: Expr VType -> TransM (Expr VType)
consEmpty e | typeOf e == pValT 
                -- Corresponds to rule [cons-empty-1]
                = return $ singletonPrim e
            
            | nestingDepth (typeOf e) > 0
                -- Corresponds to rule [cons-empty-2]
                = return $ singletonVec e
            | otherwise = error "consEmpty: Can't construct consEmpty node"
            
cons :: Expr VType -> Expr VType -> TransM (Expr VType)
cons e1 e2 | typeOf e1 == pValT && nestingDepth (typeOf e2) == 1
                -- corresponds to rule [cons-1]
                = return $ project (append (singletonPrim e1) e2) 1
            
           | nestingDepth (typeOf e1) > 0 && nestingDepth (typeOf e2) == (nestingDepth (typeOf e1)) + 1
                -- Corresponds to rule [cons-2]
                = do
                    e1a <- getFreshVar -- Variable to act as place holder for e1
                    r   <- getFreshVar -- Placeholder for append (outer $ singletonVec e1') d2
                    v   <- getFreshVar 
                    p1  <- getFreshVar
                    p2  <- getFreshVar
                    
                    let e1' = Var (typeOf e1) e1a -- Construct the actual placeholder variable for e1
                    
                    (b2, d2, vs2) <- patV e2   -- Pattern matching on e2: <d2, vs2> = e2
                    
                    let rv = append (outer (singletonVec e1')) d2
                    let r' = Var (typeOf rv) r
                    
                    let vv = project r' 1
                    let v' = Var (typeOf vv) v
                    
                    let p1v = project r' 2
                    let p1' = Var (typeOf p1v) p1
                    
                    let p2v = project r' 3
                    let p2' = Var (typeOf p2v) p2
                    
                    r1 <- renameOuter p1' e1'
                    r2 <- renameOuter p2' vs2
                    e3 <- appendR r1 r2
                    
                    return $ letF e1a e1 (b2 (letF r rv (letF v vv (letF p1 p1v (letF p2 p2v (attach v' e3))))))  
            | otherwise = error "cons: Can't construct cons node"                 

consLift :: Expr VType -> Expr VType -> TransM (Expr VType)
consLift e1 e2 | nestingDepth (typeOf e1) == 1 && nestingDepth (typeOf e2) == 2
                      -- Case that e1 has a nesting depth of 1
                    = do
                        (b1, d2, vs2) <- patV e2
                        return $ b1 $ attach d2 (project (append (segment e1) vs2) 1)
               
               | nestingDepth (typeOf e1) > 1 && nestingDepth (typeOf e2) == (nestingDepth (typeOf e1)) + 1
                      -- Case that e1 has a nesting depth > 1
                    = do
                        (b1, d1, vs1) <- patV e1
                        (b2, d2, vs2) <- patV e2
                        
                        r  <- getFreshVar
                        v  <- getFreshVar
                        p1 <- getFreshVar
                        p2 <- getFreshVar
                        
                        let rv = append (segment d1) (outer vs2)
                        let r' = Var (typeOf rv) r
                        
                        let vv = project r' 1
                        let v' = Var (typeOf vv) v
                        
                        let p1v = project r' 2
                        let p1' = Var (typeOf p1v) p1
                        
                        let p2v = project r' 3
                        let p2' = Var (typeOf p2v) p2
                        
                        r1 <- renameOuter p1' vs1
                        r2 <- renameOuter p2' (extract vs2 1) 
                        e3 <- r1 `appendR` r2
                        return $ b1 (b2 (letF r rv (letF v vv (letF p1 p1v (letF p2 p2v (attach d2 (attach v' e3)))))))
                
               | otherwise = error "consLift: Can't construct consLift node" 

restrict :: Expr VType -> Expr VType -> TransM (Expr VType)
restrict e1 e2 | nestingDepth (typeOf e1) == 1 && nestingDepth (typeOf e2) == 1
                      -- Corresponds to compilation rule [restrict-1]
                    = return $ project (restrictVec e1 e2) 1
         
               | nestingDepth (typeOf e1) > 1 && nestingDepth (typeOf e2) == 1
                      -- Corresponds to compilation rule [restrict-2]
                    = do
                        (b1, d1, vs1) <- patV e1
                        
                        r <- getFreshVar
                        v <- getFreshVar
                        p <- getFreshVar
                        
                        let rv = restrictVec d1 e2
                        let r' = Var (typeOf rv) r
                        
                        let vv = project r' 1
                        let v' = Var (typeOf vv) v
                        
                        let pv = project r' 2
                        let p' = Var (typeOf pv) p
                        
                        e3 <- chainPropagate p' vs1
                        
                        return $ b1 (letF r rv (letF v vv (letF p pv (attach v' e3))))                        
               | otherwise = error $ "restrict: Can't construct restrict node " ++ show e1 ++ show (typeOf e1) ++ " " ++ show e2 ++ show (typeOf e2) 
               
combine :: Expr VType -> Expr VType -> Expr VType -> TransM (Expr VType)
combine eb e1 e2 | nestingDepth (typeOf eb) == 1 && nestingDepth (typeOf e1) == 1 && nestingDepth (typeOf e2) == 1
                      -- Corresponds to compilation rule [combine-1]
                    = return $ project (combineVec eb e1 e2) 1
                 
                 | nestingDepth (typeOf eb) == 1 && nestingDepth (typeOf e1) > 1 && typeOf e1 == typeOf e2
                      -- Corresponds to compilation rule [combine-2]
                    = do
                        (b1, d1, vs1) <- patV e1
                        (b2, d2, vs2) <- patV e2
                        
                        r <- getFreshVar
                        v <- getFreshVar
                        p1 <- getFreshVar
                        p2 <- getFreshVar
                        
                        let rv = combineVec eb d1 d2
                        let r' = Var (typeOf rv) r
                        
                        let vv = project r' 1
                        let v' = Var (typeOf vv) v
                        
                        let p1v = project r' 2
                        let p1' = Var (typeOf p1v) p1
                        
                        let p2v = project r' 3
                        let p2' = Var (typeOf p2v) p2
                        
                        r1 <- renameOuter p1' vs1
                        r2 <- renameOuter p2' vs2
                        e3 <- appendR r1 r2
                        
                        return $ b1 (b2 (letF r rv (letF v vv (letF p1 p1v (letF p2 p2v (attach v' e3))))))
                 | otherwise = error "combine: Can't construct combine node"
                 
bPermute :: Expr VType -> Expr VType -> TransM (Expr VType)
bPermute e1 e2 | nestingDepth (typeOf e1) == 1 && nestingDepth (typeOf e2) == 1
                    = return (project (bPermuteVec e1 e2) 1)
               | otherwise = error "bPermute: Can't construct bPermute node"

runVectorise :: Expr T.Type -> TransM (Expr VType)
runVectorise e = vectorise e 
                        
vectorise :: Expr T.Type -> TransM (Expr VType)
vectorise (Labeled s e) = Labeled s <$> vectorise e
vectorise (Const t v) = return $ Const (vectoriseType t) v
vectorise (Nil t)     = return $ Nil $ tag (vectoriseType t) t
vectorise (Var t x) = return $ Var (vectoriseType t) x
vectorise (Proj t l e i) = do
                            e' <- vectorise e
                            return $ Proj (vectoriseType t) l e' i
vectorise (BinOp t o e1 e2) = case o of
                                    (Op ":" 0) -> case e2 of
                                                    (Nil _) -> do {e1' <- vectorise e1; consEmpty e1'}
                                                    _       -> do {e1' <- vectorise e1; e2' <- vectorise e2; cons e1' e2'}
                                    (Op ":" 1) -> do {e1' <- vectorise e1; e2' <- vectorise e2; consLift e1' e2'}
                                    _    -> BinOp (vectoriseType t) o <$> vectorise e1 <*> vectorise e2
                                --case of cons
vectorise (If t eb e1 e2) | T.listDepth t > 1 = do
                                                    qb <- vectorise eb
                                                    q1 <- vectorise e1
                                                    q2 <- vectorise e2
                                                    ifVec qb q1 q2
                          | otherwise = If (vectoriseType t) <$> vectorise eb <*> vectorise e1 <*> vectorise e2
vectorise (Let t s e1 e2) = Let (vectoriseType t) s <$> vectorise e1 <*> vectorise e2
vectorise (Lam t a e) = Lam (vectoriseType t) a <$> vectorise e
vectorise (App t e es) = case e of
                            (Var _ "dist")         -> do
                                                         [e1, e2] <- mapM vectorise es
                                                         dist e1 e2
                            (Var _ "dist_L")          -> do
                                                         [e1, e2] <- mapM vectorise es
                                                         distL e1 e2
                            (Var _ "restrict")     -> do
                                                         [e1, e2] <- mapM vectorise es
                                                         restrict e1 e2
                            (Var _ "combine")      -> do
                                                         [e1, e2, e3] <- mapM vectorise es
                                                         combine e1 e2 e3
                            (Var _ "back_Permute") -> do
                                                         [e1, e2] <- mapM vectorise es
                                                         bPermute e1 e2
                            _                        -> App (vectoriseType t) <$> vectorise e <*> mapM vectorise es
                                                         
