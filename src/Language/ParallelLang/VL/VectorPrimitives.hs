module Language.ParallelLang.VL.VectorPrimitives where

import Language.ParallelLang.VL.Data.VectorTypes
import Language.ParallelLang.FKL.Data.FKL
import Language.ParallelLang.FKL.Render.Render
import Language.ParallelLang.Translate.TransM

import Language.ParallelLang.Common.Data.Type(typeOf, Typed)
import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Common.Data.Val

-- * Vector primitive constructor functions

notV :: Expr VType -> Expr VType
notV e | typeOf e == pValT = App pValT (Var (pValT .~> pValT) "not" 0) [e]
       | otherwise = error "Can't construct not node"

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
                        = let rt = tupleT [typeOf e2, propT]
                           in App rt (Var (typeOf e1 .~> typeOf e2 .~> rt) "propagateIn" 0) [e1, e2]
                  | otherwise = error "propagateIn: Can't construct propagateIn node"

rename :: Expr VType -> Expr VType -> Expr VType
rename e1 e2 | typeOf e1 == propT && descrOrVal (typeOf e2)
                        = App (typeOf e2) (Var (typeOf e1 .~> typeOf e2 .~> typeOf e1) "rename" 0) [e1, e2]
             | otherwise = error $ "rename: Can't construct rename node "

attach :: Expr VType -> Expr VType -> Expr VType
attach e1 e2 | typeOf e1 == descrT && nestingDepth (typeOf e2) > 0
                        = let rt = nVectorT' (typeOf e2)
                           in App rt (Var (typeOf e1 .~> typeOf e2 .~> rt) "attach" 0) [e1, e2]
             | otherwise = error $ "attach: Can't construct attach node "
singletonPrim :: Expr VType -> Expr VType
singletonPrim e1 | typeOf e1 == pValT = App valVT (Var (typeOf e1 .~> valVT) "singletonPrim" 0) [e1]
                 | otherwise = error "singletonPrim: Can't construct singletonPrim node"

singletonVec :: Expr VType -> Expr VType
singletonVec e1 | nestingDepth (typeOf e1) > 0
                    = let rt = nVectorT' (typeOf e1)
                       in App rt (Var (typeOf e1 .~> rt) "singletonVec" 0) [e1]
                | otherwise = error "singletonVec: Can't construct singletonVec node"

append :: Expr VType -> Expr VType -> Expr VType
append e1 e2 | descrOrVal (typeOf e1) && descrOrVal (typeOf e2) && nestingDepth (typeOf e1) == nestingDepth (typeOf e2)
                    = let rt = tupleT [typeOf e1, propT, propT]
                       in App rt (Var (typeOf e1 .~> typeOf e2 .~> rt) "append" 0) [e1, e2]
             | otherwise = error $ "append: Can't construct append node" ++ show (typeOf e1) ++ " XXX " ++ show (typeOf e2)

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

bPermuteVec :: Expr VType -> Expr VType -> Expr VType
bPermuteVec e1 e2 | descrOrVal (typeOf e1) && nestingDepth (typeOf e2) == 1
                        = let rt = tupleT [typeOf e1, propT]
                           in App rt (Var (typeOf e1 .~> typeOf e2 .~> rt) "bPermute" 0) [e1, e2]
                  | otherwise = error "bPermute: Can't construct bPermute node"

extract :: Expr VType -> Int -> Expr VType
extract e i | nestingDepth (typeOf e) > i && nestingDepth (typeOf e) > 1 && i > 0
                        = let rt = nVectorT (nestingDepth (typeOf e) - i)
                           in App rt (Var (typeOf e .~> pValT .~> rt) "extract" 0) [e, intV i]
            | otherwise = error "extract: Can't construct extract node"

intV :: Int -> Expr VType
intV i = Const pValT (Int i)


-- * meta construction functions

-- | Create a tuple projection node
project :: Expr VType -> Int -> Expr VType
project e i = let t = typeOf e
                in case t of
                    (Tuple ts) -> if length ts >= i 
                                            then Proj (ts !! (i - 1)) 0 e i
                                            else error "Provided tuple expression is not big enough"
                    _                -> error "Provided type is not a tuple"


ifVec :: Expr VType -> Expr VType -> Expr VType -> TransM (Expr VType)
ifVec qb q1 q2 | typeOf qb == pValT && nestingDepth (typeOf q1) > 1 && typeOf q1 == typeOf q2
                        = do
                            d1 <- getFreshVar
                            p1 <- getFreshVar
                            d2 <- getFreshVar
                            p2 <- getFreshVar
                            ir1 <- getFreshVar
                            ir2 <- getFreshVar
                            (b1, q1', vs1) <- patV q1
                            (b2, q2', vs2) <- patV q2
                            let res1 = restrictVec q1' (distDesc qb q1')
                            let res2 = restrictVec q2' (distDesc (notV qb) q2')
                            let ir1' = Var (typeOf res1) ir1 0
                            let ir2' = Var (typeOf res2) ir2 0
                            let d1v = project ir1' 1
                            let d1'  = Var (typeOf d1v) d1 0
                            let p1v = project ir1' 2
                            let p1' = Var (typeOf p1v) p1 0
                            let d2v = project ir2' 1
                            let d2' = Var (typeOf d2v) d2 0
                            let p2v = project ir2' 2
                            let p2' = Var (typeOf p2v) p2 0
                            r1 <- renameOuter p1' vs1
                            r2 <- renameOuter p2' vs2
                            e3 <- appendR r1 r2
                            let d = flip project 1 $ append d1' d2'
                            return $ b1 (b2 (letF ir1 res1 (letF ir2 res2 (letF p1 p1v (letF d1 d1v (letF p2 p2v (letF d2 d2v (attach d e3)))))))) 
               | otherwise = error "Can't construct ifVec node"
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
                     | otherwise = error "chainPropagate: Can't expand meta rule chainPropagate" 

-- | Pattern matching. 
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
        | otherwise = error "patV: Can't perform pattern match on a nesting depth smaller than 2"

-- | Append two vectors
appendR :: Expr VType -> Expr VType -> TransM (Expr VType)
appendR e1 e2 | nestingDepth (typeOf e1) == 1 && nestingDepth (typeOf e2) == 1
                    = return $ flip project 1 $ append e1 e2
              | nestingDepth (typeOf e1) > 1 && nestingDepth (typeOf e1) == nestingDepth (typeOf e2)
                    = do
                        r <- getFreshVar
                        v <- getFreshVar
                        p1 <- getFreshVar
                        p2 <- getFreshVar
                        (b1, d1, vs1) <- patV e1
                        (b2, d2, vs2) <- patV e2
                        let rv = append d1 d2
                        let r' = Var (typeOf rv) r 0
                        let vv = project r' 1
                        let v' = Var (typeOf vv) v 0
                        let p1v = project r' 2
                        let p1' = Var (typeOf p1v) p1 0
                        let p2v = project r' 3
                        let p2' = Var (typeOf p2v) p2 0
                        r1 <- renameOuter p1' vs1
                        r2 <- renameOuter p2' vs2
                        rec <- appendR r1 r2
                        return $ b1 (b2 (letF r rv (letF v vv (letF p1 p1v (letF p2 p2v (attach v' rec))))))
              | otherwise = error $ "appendR: Can't expand meta function appendR "

-- | Apply renaming to the outermost vector
renameOuter :: Expr VType -> Expr VType -> TransM (Expr VType)
renameOuter p e | typeOf p == propT && nestingDepth (typeOf e) == 1
                    = return $ rename p e
                | typeOf p == propT && nestingDepth (typeOf e) > 1
                    = do
                        (b, h, t) <- patV e
                        return $ b (attach (rename p h) t)
                | otherwise = error "renameOuter: Can't expand meta renameOuter rule"
