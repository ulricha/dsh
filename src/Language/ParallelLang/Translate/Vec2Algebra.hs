{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.Translate.Vec2Algebra (toAlgebra, toXML) where

import Language.ParallelLang.Common.Data.Val
import Database.Ferry.Algebra hiding (getLoop, withContext, Gam)
import qualified Database.Ferry.Algebra as A
import Language.ParallelLang.FKL.Data.FKL
import qualified Language.ParallelLang.VL.Data.VectorTypes as T
import Language.ParallelLang.Common.Data.Op
import qualified Language.ParallelLang.Common.Data.Type as U
import Language.ParallelLang.VL.Data.Query
import Database.Ferry.Algebra.Render.XML hiding (XML, Graph)
import qualified Language.ParallelLang.Common.Data.Type as Ty

import qualified Data.Map as M
import Control.Applicative hiding (Const)

import Language.ParallelLang.Common.Impossible

type Graph = GraphM Plan

type Gam = A.Gam Plan

type Plan = Query AlgNode

-- | Results are stored in column:
pos, item1, descr, descr', descr'', pos', pos'', pos''', posold, posnew, ordCol, resCol, tmpCol, tmpCol' :: String
pos       = "pos"
item1     = "item1"
descr     = "iter"
descr'    = "item99999501"
descr''   = "item99999502"
pos'      = "item99999601"
pos''     = "item99999602"
pos'''    = "item99999603"
posold    = "item99999604"
posnew    = "item99999605"
ordCol    = "item99999801"
resCol    = "item99999001"
tmpCol    = "item99999002"
tmpCol'   = "item99999003"

fkl2Alg :: Expr Ty.Type -> Graph Plan
fkl2Alg (Labeled s e) = fkl2Alg e
fkl2Alg (Const _ v) = PrimVal <$> (tagM "constant" $ (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ val2Alg v))

consEmpty :: Plan -> Graph Plan
consEmpty q@(PrimVal _) = singletonPrim q -- Corresponds to rule [cons-empty-1]
consEmpty q | nestingDepth q > 0 = singletonVec q
            | otherwise = error "consEmpty: Can't construct consEmpty node"

cons :: Plan -> Plan -> Graph Plan
cons q1@(PrimVal _) q2@(ValueVector _)
                -- corresponds to rule [cons-1]
                = do
                    n <- singletonPrim q1
                    TupleVector [v, _, _] <- append n q2
                    return v
cons q1 q2@(NestedVector d2 vs2) | nestingDepth q1 > 0 && nestingDepth q2 == (nestingDepth q1) + 1
                -- Corresponds to rule [cons-2]
                = do
                    o <- (singletonVec q1) >>= outer
                    TupleVector [v, p1, p2] <- append o (DescrVector d2)
                    r1 <- renameOuter p1 q1
                    r2 <- renameOuter p2 vs2
                    e3 <- appendR r1 r2
                    return $ attachV v e3
            | otherwise = error "cons: Can't construct cons node"

-- | Apply renaming to the outermost vector
renameOuter :: Plan -> Plan -> Graph Plan
renameOuter p@(PropVector _) e@(ValueVector _)
                                = rename p e
renameOuter p@(PropVector _) e@(NestedVector h t)
                                = do
                                    d <- rename p (DescrVector h)
                                    return $ attachV d t

consLift :: Plan -> Plan -> Graph Plan
consLift e1@(ValueVector _) e2@(NestedVector d2 vs2) | nestingDepth e2 == 2
                      -- Case that e1 has a nesting depth of 1
                    = do
                        s <- segment e1
                        TupleVector [v, _, _] <- append s vs2
                        return $ attachV (DescrVector d2) v
consLift e1@(NestedVector d1 vs1) e2@(NestedVector d2 vs2) 
               | nestingDepth e1 > 1 && nestingDepth e2 == (nestingDepth e1) + 1
                      -- Case that e1 has a nesting depth > 1
                    = do
                        s <- segment (DescrVector d1)
                        o <- outer vs2
                        TupleVector [v, p1, p2] <- append s o
                        r1 <- renameOuter p1 vs1
                        vs2' <- extract vs2 1
                        r2 <- renameOuter p2 vs2'
                        e3 <- appendR r1 r2
                        return $ attachV (DescrVector d2) $ attachV v e3
               | otherwise = error "consLift: Can't construct consLift node"

restrict :: Plan -> Plan -> Graph Plan
restrict e1@(ValueVector _) e2@(ValueVector _) 
                     -- Corresponds to compilation rule [restrict-1]
                   = do
                        TupleVector [v, _] <- restrictVec e1 e2
                        return v

restrict (NestedVector d1 vs1) e2@(ValueVector _)
                     -- Corresponds to compilation rule [restrict-2]
                   = do
                       TupleVector [v, p] <- restrictVec (DescrVector d1) e2
                       e3 <- chainPropagate p vs1
                       return $ attachV v e3
restrict e1 e2 = error $ "restrict: Can't construct restrict node " ++ show e1 ++ " " ++ show e2

combine :: Plan -> Plan -> Plan -> Graph Plan
combine eb e1 e2 | nestingDepth eb == 1 && nestingDepth e1 == 1 && nestingDepth e2 == 1
                      -- Corresponds to compilation rule [combine-1]
                    = do
                        TupleVector [v, _, _] <- combineVec eb e1 e2
                        return v
                 | nestingDepth eb == 1 && nestingDepth e1 > 1 && nestingDepth e1 == nestingDepth e2
                      -- Corresponds to compilation rule [combine-2]
                    = do
                        let (NestedVector d1 vs1) = e1
                        let (NestedVector d2 vs2) = e2
                        TupleVector [v, p1, p2] <- combineVec eb (DescrVector d1) (DescrVector d2)
                        r1 <- renameOuter p1 vs1
                        r2 <- renameOuter p2 vs2
                        e3 <- appendR r1 r2
                        return $ attachV v e3
                 | otherwise = error "combine: Can't construct combine node"

bPermute :: Plan -> Plan -> Graph Plan
bPermute e1 e2 | nestingDepth e1 == 1 && nestingDepth e2 == 1
                    = do
                        TupleVector [v, _] <- bPermuteVec e1 e2
                        return v
               | otherwise = error "bPermute: Can't construct bPermute node"

-- | Append two vectors
appendR :: Plan -> Plan -> Graph Plan
appendR e1@(ValueVector _) e2@(ValueVector _)
                    = do
                          TupleVector [v, _] <- append e1 e2
                          return v
appendR e1@(NestedVector d1 vs1) e2@(NestedVector d2 vs2)
                    = do
                        TupleVector [v, p1, p2] <- append (DescrVector d1) (DescrVector d2)
                        e1' <- renameOuter p1 vs1
                        e2' <- renameOuter p2 vs2
                        e3 <- appendR e1' e2'
                        return $ attachV v e3

dist :: Plan -> Plan -> Graph Plan
dist q1@(PrimVal _) q2        | nestingDepth q2 > 0 = do
                                                        o <- outer q2
                                                        distPrim q1 o
                              | otherwise           = error "dist: Not a list vector"
dist q1@(ValueVector _) q2    | nestingDepth q2 > 0 = do
                                                       d2v <- outer q2
                                                       TupleVector [q1v, _] <- distDesc q1 d2v
                                                       return $ attachV d2v q1v
                              | otherwise           = error "dist: Not a list vector"
dist q1@(NestedVector _ _) q2 | nestingDepth q2 > 0 = do
                                                        o1 <- outer q1
                                                        o2 <- outer q2
                                                        TupleVector [d, p] <- distDesc o1 o2
                                                        et <- extract q1 1
                                                        e3 <- chainPropagate p et
                                                        o <- outer q2
                                                        return $ attachV o $ attachV d e3
                              | otherwise           = error "dist: Not a list vector"
dist q1@(Closure n env f fl) q2 | nestingDepth q2 > 0 = (\env' -> AClosure ((n, q2):env') f fl) <$> mapEnv (flip dist q2) env
                                                            
mapEnv :: (Plan -> Graph Plan) -> [(String, Plan)] -> Graph [(String, Plan)]
mapEnv f ((x, p):xs) = (\p' xs' -> (x, p'):xs') <$> f p <*> mapEnv f xs
mapEnv f []          = return []


                         
distL :: Plan -> Plan -> Graph (Plan)
distL q1@(ValueVector _) (NestedVector d vs) = do
                                                o <- outer vs
                                                TupleVector [v, _] <- distLift q1 o
                                                return $ attachV (DescrVector d) v
distL (NestedVector d1 vs1) (NestedVector d2 vs2) = do 
                                                     o <- outer vs2
                                                     TupleVector [d, p] <- distLift (DescrVector d1) o
                                                     e3 <- chainPropagate p vs1
                                                     return $ attachV (DescrVector d2) $ attachV d e3
distL (AClosure ((n,v):xs) f fl) q2 = do
                                        v' <- dist q2 v
                                        xs' <- mapEnv (\x -> distL x v') xs
                                        return $ AClosure ((n, v'):xs') f fl
                                        
-- Closure String [(String, Query a)] (Expr T.Type) (Expr T.Type)
-- AClosure [(String, Query a)] (Expr T.Type) (Expr T.Type)

chainPropagate :: Plan -> Plan -> Graph Plan
chainPropagate p q@(ValueVector _) = do 
                                      TupleVector [v, _] <- propagateIn p q
                                      return v
chainPropagate p (NestedVector d vs) = do
                                        TupleVector [v', p'] <- propagateIn p (DescrVector d)
                                        e3 <- chainPropagate p' vs
                                        return $ attachV v' e3
                                        
toAlgebra :: Expr T.VType -> AlgPlan Plan
toAlgebra e = runGraph initLoop (vec2Alg e)

toXML :: AlgPlan Plan -> Query XML
toXML (g, r, ts) = case r of
                     (PrimVal r') -> PrimVal (XML r' $ toXML' withItem r')
                     (TupleVector rs)   -> TupleVector $ map (\r' -> toXML (g, r', ts)) rs
                     (DescrVector r') -> DescrVector (XML r' $ toXML' withoutItem r')
                     (ValueVector r') -> ValueVector (XML r' $ toXML' withItem r')
                     (NestedVector r' rs) -> NestedVector (XML r' $ toXML' withoutItem r') $ toXML (g, rs, ts)
                     (PropVector _) -> error "Prop vectors should only be used internally and never appear in a result"
--                     (UnEvaluated _) -> error "A not evaluated function can not occur in the query result"
    where
        item :: Element ()
        item = [attr "name" $ "item1", attr "new" "false", attr "function" "item", attr "position" "1"] `attrsOf` xmlElem "column"
        withItem, withoutItem :: [Element ()]
        withItem = [iterCol, posCol, item]
        withoutItem = [iterCol, posCol]
        nodeTable = M.fromList $ map (\(a, b) -> (b, a)) $ M.toList g
        toXML' :: [Element ()] -> AlgNode -> String
        toXML' cs n = show $ document $ mkXMLDocument $ mkPlanBundle $ 
                        runXML False M.empty M.empty $
                            mkQueryPlan Nothing (xmlElem "property") $ 
                                runXML True nodeTable ts $ serializeAlgebra cs n
    


val2Alg :: Val -> Graph AlgNode
val2Alg (Int i) = litTable (int $ fromIntegral i) item1 intT
val2Alg (Bool b) = litTable (bool b) item1 boolT
val2Alg Unit     = litTable (int (-1)) item1 intT  
val2Alg (String s) = litTable (string s) item1 stringT
val2Alg (Double d) = litTable (double d) item1 doubleT 

convertType :: U.Type -> ATy
convertType t | t == U.intT  = intT
              | t == U.boolT = boolT
              | t == U.unitT = intT
              | t == U.stringT = stringT
              | t == U.doubleT = doubleT
              | otherwise = error "convertType: Can't convert from DBPH type to Ferry types"


vec2Alg :: Expr T.VType -> Graph Plan
vec2Alg (Labeled _ e) = vec2Alg e
{-
vec2Alg (Const _ v) = PrimVal <$> (tagM "constant" $ (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ val2Alg v))
vec2Alg (Nil (T.Tagged vt t)) = case T.nestingDepth vt of
                            0 -> error "Invalid vector type for a Nil value"
                            1 -> ValueVector <$> (tagM "Nil" $ emptyTable [(descr, natT), (pos, natT), (item1, convertType $ U.unliftType t)])
                            n -> NestedVector <$> (tagM "Nil" $ emptyTable [(descr, natT), (pos, natT)]) <*> (tagVector "NilR" $ vec2Alg (Nil (T.Tagged (T.NestedVector (n - 1)) (U.unliftType t))))
vec2Alg (Nil _) = error "Nil without tagged type not supported"
vec2Alg (BinOp _ (Op o l) e1 e2) | o == ":" = error "Cons operations should have been desugared"
                                 | otherwise = do
                                                p1 <- vec2Alg e1
                                                p2 <- vec2Alg e2
                                                let (rt, extr) = case l of
                                                                  0 -> (PrimVal, \e -> case e of {(PrimVal q) -> q; _ -> $impossible})
                                                                  1 -> (ValueVector, \e -> case e of {(ValueVector q) -> q; _ -> $impossible})
                                                                  _ -> error "This level of liftedness should have been elimated"
                                                let q1 = extr p1
                                                let q2 = extr p2
                                                rt <$> (projM [(item1, resCol), (descr, descr), (pos, pos)] 
                                                    $ operM o resCol item1 tmpCol 
                                                        $ eqJoinM pos pos' (return q1) 
                                                            $ proj [(tmpCol, item1), (pos', pos)] q2)
vec2Alg (Proj _ _ e n) = do
                            (TupleVector es) <- vec2Alg e
                            return $ es !! (n - 1)        
vec2Alg (If t eb e1 e2) | t == T.pValT = do
                                            (PrimVal qb) <- vec2Alg eb
                                            (PrimVal q1) <- vec2Alg e1
                                            (PrimVal q2) <- vec2Alg e2
                                            b <- proj [(tmpCol, item1)] qb
                                            qr <- projM [(descr, descr), (pos, pos), (item1, item1)] $ 
                                                    selectM  tmpCol $ 
                                                        unionM (cross q1 b) $ 
                                                            crossM (return q2) $ 
                                                                projM [(tmpCol, resCol)] $ notC resCol tmpCol b
                                            return (PrimVal qr)
                        | T.nestingDepth t == 1 = do
                                                 (PrimVal qb) <- vec2Alg eb
                                                 (ValueVector q1) <- vec2Alg e1
                                                 (ValueVector q2) <- vec2Alg e2
                                                 b <- proj [(tmpCol, item1)] qb
                                                 qr <- projM [(descr, descr), (pos, pos), (item1, item1)] $ 
                                                         selectM  tmpCol $ 
                                                             unionM (cross q1 b) $ 
                                                                 crossM (return q2) $ 
                                                                     projM [(tmpCol, resCol)] $ notC resCol tmpCol b
                                                 return (ValueVector qr)
                         | otherwise = error "vec2Alg: Can't translate if construction"
vec2Alg (Let _ s e1 e2) = do
                            e1' <- tagVector s $ vec2Alg e1
                            withBinding s e1' (vec2Alg e2)
vec2Alg (Var _ s) = fromGam $ constrEnvName s i
vec2Alg (App _ (Var _ x i) args) = case x of
                                    "not" -> do
                                               let [e] = map vec2Alg args
                                               notA e
                                    "outer" -> do 
                                                let [e] = map vec2Alg args
                                                outer e
                                    "distPrim" -> do 
                                                   let [e1, e2] = map vec2Alg args
                                                   distPrim e1 e2
                                    "distDesc" -> do 
                                                   let [e1, e2] = map vec2Alg args
                                                   distDesc e1 e2
                                    "distLift" -> do 
                                                    let [e1, e2] = map vec2Alg args
                                                    distLift e1 e2
                                    "propagateIn" -> do 
                                                      let [e1, e2] = map vec2Alg args
                                                      propagateIn e1 e2
                                    "rename" -> do 
                                                 let [e1, e2] = map vec2Alg args
                                                 rename e1 e2
                                    "attach" -> do 
                                                 let [e1, e2] = map vec2Alg args
                                                 attachV e1 e2
                                    "singletonPrim" -> do 
                                                        let [e1] = map vec2Alg args
                                                        singletonPrim e1
                                    "singletonVec" -> do 
                                                       let [e1] = map vec2Alg args
                                                       singletonVec e1
                                    "append" -> do 
                                                  let [e1, e2] = map vec2Alg args
                                                  append e1 e2
                                    "segment" -> do 
                                                  let [e1] = map vec2Alg args
                                                  segment e1
                                    "restrictVec" -> do 
                                                      let [e1, e2] = map vec2Alg args
                                                      restrictVec e1 e2
                                    "combineVec" -> do 
                                                     let [e1, e2 ,e3] = map vec2Alg args
                                                     combineVec e1 e2 e3
                                    "bPermute" -> do 
                                                    let [e1, e2] = map vec2Alg args
                                                    bPermuteVec e1 e2
                                    "extract" -> do 
                                                    let [e1, e2] = args
                                                    extract (vec2Alg e1) (intFromVal e2)
                                    "insert" -> do 
                                                  let [e1, e2, e3] = args
                                                  insert (vec2Alg e1) (vec2Alg e2) (intFromVal e3)
                                    _        -> do
                                                 v <- fromGam (constrEnvName x i)
                                                 case v of
--                                                     UnEvaluated v' -> vec2Alg (App t v' args)
                                                     _              -> error $ "vec2Alg application: Not a function: " ++ show v
-}
{-
vec2Alg (App _ (Fn _ _ _ avs e) args) = do
                                         args' <- mapM vec2Alg args
                                         foldr (\(x, a) ex -> withBinding x a ex) (vec2Alg e) (zip avs args')
-}
vec2Alg _ = error "Not defined yet"
{-
data Expr t where
    App   :: t -> Expr t -> [Expr t] -> Expr t-- | Apply multiple arguments to an expression
    Fn    :: t -> String -> Int -> [String] -> Expr t -> Expr t -- | A function has a name (and lifted level), some arguments and a body
-}

notA :: Plan -> Graph Plan
notA (PrimVal q1) = PrimVal <$> projM [(pos, pos), (descr, descr), (item1, resCol)] (notC resCol item1 q1)
notA (ValueVector q1) = ValueVector <$> projM [(pos, pos), (descr, descr), (item1, resCol)] (notC resCol item1 q1)

outer :: Plan -> Graph Plan
outer (NestedVector p _) = return $ DescrVector p
outer (ValueVector p)    = DescrVector <$> (tagM "outer" $ proj [(pos, pos), (descr,descr)] p)
outer e                  = error $ "outer: Can't extract outer plan" ++ show e
                
distPrim :: Plan -> Plan -> Graph Plan
distPrim (PrimVal q1) d = do
                 (DescrVector q2) <- toDescr d
                 ValueVector <$> crossM (proj [(item1, item1)] q1) (return q2)
                  
distDesc :: Plan -> Plan -> Graph Plan
distDesc e1 e2 = do
                   (rf, q1, pf) <- determineResultVector e1
                   (DescrVector q2) <- toDescr e2
                   q <- projM (pf [(descr, pos), (pos, pos''), (posold, posold)]) $ rownumM pos'' [pos, pos'] Nothing $ crossM (proj [(pos, pos)] q2) (proj (pf [(pos', pos), (posold, pos)]) q1)
                   qr1 <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                   qr2 <- PropVector <$> proj [(posold, posold), (posnew, pos)] q
                   return $ TupleVector [qr1, qr2]

distLift :: Plan -> Plan -> Graph Plan
distLift e1 e2 = do
                    (rf, q1, pf) <- determineResultVector e1
                    (DescrVector q2) <- toDescr e2
                    q <- eqJoinM pos' descr (proj (pf [(pos', pos)]) q1) $ return q2
                    qr1 <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                    qr2 <- DescrVector <$> proj [(posold, pos'), (posnew, pos)] q
                    return $ TupleVector [qr1, qr2]                    

rename :: Plan -> Plan -> Graph Plan
rename (PropVector q1) e2 = do
                (rf, q2, pf) <- determineResultVector e2
                q <- tagM "rename" $ projM (pf [(descr, posnew), (pos, pos)]) $ eqJoin posold descr q1 q2
                return $ rf q
                
propagateIn :: Plan -> Plan -> Graph Plan
propagateIn (PropVector q1) e2 = do
                     (rf, q2, pf) <- determineResultVector e2
                     q <- rownumM pos' [posnew, pos] Nothing $ eqJoin posold descr q1 q2
                     qr1 <- rf <$> proj (pf [(descr, posnew), (pos, pos')]) q
                     qr2 <- PropVector <$> proj [(posold, pos), (posnew, pos')] q
                     return $ TupleVector [qr1, qr2]
                     
attachV :: Plan -> Plan -> Plan
attachV (DescrVector q1) e2 = NestedVector q1 e2
                
singletonPrim :: Plan -> Graph Plan
singletonPrim (PrimVal q1) = do
                    return $ ValueVector q1
                    
singletonVec :: Plan -> Graph Plan
singletonVec e1 = do
                    q <- tagM "singletonVec" $ attachM pos natT (nat 1) $ litTable (nat 1) descr natT
                    return $ NestedVector q e1
                    
append :: Plan -> Plan -> Graph Plan
append e1 e2 = do
                (rf, q1, q2, pf) <- determineResultVector' e1 e2
                q <- rownumM pos' [descr, ordCol, pos] Nothing $ attach ordCol natT (nat 1) q1 `unionM` attach ordCol natT (nat 2) q2
                qv <- rf <$> tagM "append r" (proj (pf [(pos, pos'), (descr, descr)]) q)
                qp1 <- PropVector <$> (tagM "append r1" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 1) q)
                qp2 <- PropVector <$> (tagM "append r2" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 2) q)
                return $ TupleVector [qv, qp1, qp2]
                

segment :: Plan -> Graph Plan
segment e = do
             (rf, q, pf) <- determineResultVector e
             rf <$> proj (pf [(descr, pos), (pos, pos)]) q

extract :: Plan -> Int -> Graph Plan
extract p 0 = return p
extract (NestedVector _ p') n | n > 0 = extract p' (n - 1)

insert :: Plan -> Plan -> Int -> Graph Plan
insert p _ 0 = return p
insert p d n | n > 0 = do
                        o <- outer d
                        d' <- extract d 1
                        insert (attachV o p) d' (n - 1)
             | otherwise = error "Can't insert a negative amount of descriptors"

restrictVec :: Plan -> Plan -> Graph Plan
restrictVec e1 (ValueVector qm) = do
                    (rf, q1, pf) <- determineResultVector e1
                    q <- rownumM pos'' [pos] Nothing $ selectM resCol $ eqJoinM pos pos' (return q1) $ proj [(pos', pos), (resCol, item1)] qm
                    qr <- rf <$> proj (pf [(pos, pos''), (descr, descr)]) q
                    qp <- PropVector <$> proj [(posold, pos), (posnew, pos'')] q
                    return $ TupleVector [qr, qp]

combineVec :: Plan -> Plan -> Plan -> Graph Plan
combineVec (ValueVector qb) e1 e2 = do
                        (rf, q1, q2, pf) <- determineResultVector' e1 e2
                        d1 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ select item1 qb
                        d2 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ selectM resCol $ notC resCol item1 qb
                        q <- eqJoinM pos' posold (return d1) (proj (pf [(posold, pos), (descr, descr)]) q1) `unionM` eqJoinM pos' posold (return d2) (proj (pf [(posold, pos), (descr, descr)]) q2)
                        qr <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                        qp1 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d1
                        qp2 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d2
                        return $ TupleVector [qr, qp1, qp2]
                        
bPermuteVec :: Plan -> Plan -> Graph Plan
bPermuteVec e1 (ValueVector q2) = do
                     (rf, q1, pf) <- determineResultVector e1
                     q <- eqJoinM pos pos' (return q1) $ proj [(pos', pos), (posnew, item1)] q2
                     qr <- rf <$> proj (pf [(descr, descr), (pos, posnew)]) q
                     qp <- PropVector <$> proj [(posold, pos), (posnew, posnew)] q
                     return $ TupleVector [qr, qp]

determineResultVector :: Plan -> Graph (AlgNode -> Plan, AlgNode, ProjInf -> ProjInf)
determineResultVector e = do
                            let hasI = isValueVector e
                            let rf = if hasI then ValueVector else DescrVector
                            let pf = if hasI then \x -> (item1, item1):x else \x -> x
                            let q = if hasI
                                        then let (ValueVector q') = e in q'
                                        else let (DescrVector q') = e in q'
                            return (rf, q, pf)

determineResultVector' :: Plan -> Plan -> Graph (AlgNode -> Plan, AlgNode, AlgNode, ProjInf -> ProjInf)
determineResultVector' e1 e2 = do
                                let hasI = isValueVector e1
                                let rf = if hasI then ValueVector else DescrVector
                                let pf = if hasI then \x -> (item1, item1):x else \x -> x
                                let (q1, q2) = if hasI
                                                then let (ValueVector q1') = e1
                                                         (ValueVector q2') = e2 in (q1', q2')
                                                else let (DescrVector q1') = e1 
                                                         (DescrVector q2') = e2 in (q1', q2')
                                return (rf, q1, q2, pf)

toDescr :: Plan -> Graph Plan
toDescr v@(DescrVector _) = return v
toDescr (ValueVector n)   = DescrVector <$> tagM "toDescr" (proj [(descr, descr), (pos, pos)] n)

isValueVector :: Plan -> Bool
isValueVector (ValueVector _) = True
isValueVector _               = False

-- | Construct a name that represents a lifted variable in the environment.                        
constrEnvName :: String -> Int -> String
constrEnvName x 0 = x
constrEnvName x i = x ++ "<%>" ++ show i

intFromVal :: Expr T.VType -> Int
intFromVal (Const _ (Int i)) = i
intFromVal x                 = error $ "intFromVal: not an integer: " ++ show x

tagVector :: String -> Plan -> Graph Plan
tagVector s (TupleVector vs) = TupleVector <$> (sequence $ map (\v -> tagVector s v) vs)
tagVector s (DescrVector q) = DescrVector <$> tag s q
tagVector s (ValueVector q) = ValueVector <$> tag s q
tagVector s (PrimVal q) = PrimVal <$> tag s q
tagVector s (NestedVector q qs) = NestedVector <$> tag s q <*> tagVector s qs
tagVector s (PropVector q) = PropVector <$> tag s q
