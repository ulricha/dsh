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
consEmpty q@(PrimVal _) = singletonPrim $ return q -- Corresponds to rule [cons-empty-1]
consEmpty q | nestingDepth q > 0 = singletonVec $ return q
            | otherwise = error "consEmpty: Can't construct consEmpty node"

cons :: Plan -> Plan -> Graph Plan
cons q1@(PrimVal _) q2@(ValueVector _)
                -- corresponds to rule [cons-1]
                = do
                    TupleVector [v, _, _] <- append (singletonPrim (return q1)) (return q2)
                    return v
cons q1 q2@(NestedVector d2 vs2) | nestingDepth q1 > 0 && nestingDepth q2 == (nestingDepth q1) + 1
                -- Corresponds to rule [cons-2]
                = do
                    TupleVector [v, p1, p2] <- append (outer $ singletonVec $ return q1) (return $ DescrVector d2)
                    r1 <- renameOuter p1 q1
                    r2 <- renameOuter p2 vs2
                    e3 <- appendR r1 r2
                    attachV (return v) (return e3)
            | otherwise = error "cons: Can't construct cons node"

-- | Apply renaming to the outermost vector
renameOuter :: Plan -> Plan -> Graph Plan
renameOuter p@(PropVector _) e@(ValueVector _)
                                = rename (return p) (return e)
renameOuter p@(PropVector _) e@(NestedVector h t)
                                = attachV (rename (return p) (return $ DescrVector h)) (return t)

-- | Append two vectors
appendR :: Plan -> Plan -> Graph Plan
appendR e1@(ValueVector _) e2@(ValueVector _)
                    = do
                          TupleVector [v, _] <- append (return e1) (return e2)
                          return v
appendR e1@(NestedVector d1 vs1) e2@(NestedVector d2 vs2)
                    = do
                        TupleVector [v, p1, p2] <- append (return $ DescrVector d1) (return $ DescrVector d2)
                        e1' <- renameOuter p1 vs1
                        e2' <- renameOuter p2 vs2
                        e3 <- appendR e1' e2'
                        attachV (return v) (return e3)

dist :: Plan -> Plan -> Graph Plan
dist q1@(PrimVal _) q2        | nestingDepth q2 > 0 = distPrim (return q1) (outer $ return q2)
                              | otherwise           = error "dist: Not a list vector"
dist q1@(ValueVector _) q2    | nestingDepth q2 > 0 = do
                                                       d2v <- outer (return q2)
                                                       TupleVector [q1v, _] <- distDesc (return q1) (return d2v)
                                                       attachV (return d2v) (return q1v)
                              | otherwise           = error "dist: Not a list vector"
dist q1@(NestedVector _ _) q2 | nestingDepth q2 > 0 = do
                                                        TupleVector [d, p] <- distDesc (outer $ return q1) (outer $ return q2)
                                                        et <- extract (return q1) 1
                                                        attachV (outer $ return q2) $ attachV (return d) (chainPropagate p et)
                              | otherwise           = error "dist: Not a list vector"

dist q1@(Closure n env f fl) q2 | nestingDepth q2 > 0 = (\env' -> AClosure ((n, q2):env') f fl) <$> mapEnv (flip dist q2) env
                                                            
mapEnv :: (Plan -> Graph Plan) -> [(String, Plan)] -> Graph [(String, Plan)]
mapEnv f ((x, p):xs) = (\p' xs' -> (x, p'):xs') <$> f p <*> mapEnv f xs
mapEnv f []          = return []


                         
distL :: Plan -> Plan -> Graph (Plan)
distL q1@(ValueVector _) (NestedVector d vs) = do
                                                TupleVector [v, _] <- distLift (return q1) (outer $ return vs)
                                                attachV (return $ DescrVector d) (return v)
distL (NestedVector d1 vs1) (NestedVector d2 vs2) = do 
                                                     TupleVector [d, p] <- distLift (return $ DescrVector d1) (outer $ return vs2)
                                                     e3 <- chainPropagate p vs1
                                                     attachV (return $ DescrVector d2) $ attachV (return d) (return e3)
distL (AClosure ((n,v):xs) f fl) q2 = do
                                        v' <- dist q2 v
                                        xs' <- mapEnv (\x -> distL x v') xs
                                        return $ AClosure ((n, v'):xs') f fl
                                        
-- Closure String [(String, Query a)] (Expr T.Type) (Expr T.Type)
-- AClosure [(String, Query a)] (Expr T.Type) (Expr T.Type)

chainPropagate :: Plan -> Plan -> Graph Plan
chainPropagate p q@(ValueVector _) = do 
                                      TupleVector [v, _] <- propagateIn (return p) (return q)
                                      return v
chainPropagate p (NestedVector d vs) = do
                                        TupleVector [v', p'] <- propagateIn (return p) (return $ DescrVector d)
                                        attachV (return v') $ chainPropagate p' vs
                                        
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

notA :: Graph Plan -> Graph Plan
notA e = do
           e' <- e
           case e' of
               (PrimVal q1) -> PrimVal <$> projM [(pos, pos), (descr, descr), (item1, resCol)] (notC resCol item1 q1)
               (ValueVector q1) -> ValueVector <$> projM [(pos, pos), (descr, descr), (item1, resCol)] (notC resCol item1 q1)
outer :: Graph Plan -> Graph Plan
outer e = do
            e' <- e
            case e' of
                NestedVector p _  -> return $ DescrVector p
                (ValueVector p) -> DescrVector <$> (tagM "outer" $ proj [(pos, pos), (descr,descr)] p)
                _                 -> error $ "outer: Can't extract outer plan" ++ show e'
                
distPrim :: Graph Plan -> Graph Plan -> Graph Plan
distPrim v d = do
                 (PrimVal q1) <- v
                 (DescrVector q2) <- toDescr d
                 ValueVector <$> crossM (proj [(item1, item1)] q1) (return q2)
                  
distDesc :: Graph Plan -> Graph Plan -> Graph Plan
distDesc e1 e2 = do
                   (rf, q1, pf) <- determineResultVector e1
                   (DescrVector q2) <- toDescr e2
                   q <- projM (pf [(descr, pos), (pos, pos''), (posold, posold)]) $ rownumM pos'' [pos, pos'] Nothing $ crossM (proj [(pos, pos)] q2) (proj (pf [(pos', pos), (posold, pos)]) q1)
                   qr1 <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                   qr2 <- PropVector <$> proj [(posold, posold), (posnew, pos)] q
                   return $ TupleVector [qr1, qr2]

distLift :: Graph Plan -> Graph Plan -> Graph Plan
distLift e1 e2 = do
                    (rf, q1, pf) <- determineResultVector e1
                    (DescrVector q2) <- toDescr e2
                    q <- eqJoinM pos' descr (proj (pf [(pos', pos)]) q1) $ return q2
                    qr1 <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                    qr2 <- DescrVector <$> proj [(posold, pos'), (posnew, pos)] q
                    return $ TupleVector [qr1, qr2]                    

rename :: Graph Plan -> Graph Plan -> Graph Plan
rename e1 e2 = do
                (PropVector q1) <- e1
                (rf, q2, pf) <- determineResultVector e2
                q <- tagM "rename" $ projM (pf [(descr, posnew), (pos, pos)]) $ eqJoin posold descr q1 q2
                return $ rf q
                
propagateIn :: Graph Plan -> Graph Plan -> Graph Plan
propagateIn e1 e2 = do
                     (PropVector q1) <- e1
                     (rf, q2, pf) <- determineResultVector e2
                     q <- rownumM pos' [posnew, pos] Nothing $ eqJoin posold descr q1 q2
                     qr1 <- rf <$> proj (pf [(descr, posnew), (pos, pos')]) q
                     qr2 <- PropVector <$> proj [(posold, pos), (posnew, pos')] q
                     return $ TupleVector [qr1, qr2]
                     
attachV :: Graph Plan -> Graph Plan -> Graph Plan
attachV e1 e2 = do
                 (DescrVector q1) <- e1
                 e2' <- e2
                 return $ NestedVector q1 e2'
                
singletonPrim :: Graph Plan -> Graph Plan
singletonPrim e1 = do
                    (PrimVal q1) <- e1
                    return $ ValueVector q1
                    
singletonVec :: Graph Plan -> Graph Plan
singletonVec e1 = do
                    e1' <- e1
                    q <- tagM "singletonVec" $ attachM pos natT (nat 1) $ litTable (nat 1) descr natT
                    return $ NestedVector q e1'
                    
append :: Graph Plan -> Graph Plan -> Graph Plan
append e1 e2 = do
                (rf, q1, q2, pf) <- determineResultVector' e1 e2
                q <- rownumM pos' [descr, ordCol, pos] Nothing $ attach ordCol natT (nat 1) q1 `unionM` attach ordCol natT (nat 2) q2
                qv <- rf <$> tagM "append r" (proj (pf [(pos, pos'), (descr, descr)]) q)
                qp1 <- PropVector <$> (tagM "append r1" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 1) q)
                qp2 <- PropVector <$> (tagM "append r2" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 2) q)
                return $ TupleVector [qv, qp1, qp2]
                

segment :: Graph Plan -> Graph Plan
segment e = do
             (rf, q, pf) <- determineResultVector e
             rf <$> proj (pf [(descr, pos), (pos, pos)]) q

extract :: Graph Plan -> Int -> Graph Plan
extract p 0 = p
extract p n | n > 0 = do
                       (NestedVector _ p') <- p
                       extract (return p') (n - 1)
            | otherwise = error "Can't extract a negative amount of descriptors"

insert :: Graph Plan -> Graph Plan -> Int -> Graph Plan
insert p _ 0 = p
insert p d n | n > 0 = insert (attachV (outer d) p) (extract d 1) (n - 1)
             | otherwise = error "Can't insert a negative amount of descriptors"

restrictVec :: Graph Plan -> Graph Plan -> Graph Plan
restrictVec e1 m = do
                    (rf, q1, pf) <- determineResultVector e1
                    (ValueVector qm) <- m
                    q <- rownumM pos'' [pos] Nothing $ selectM resCol $ eqJoinM pos pos' (return q1) $ proj [(pos', pos), (resCol, item1)] qm
                    qr <- rf <$> proj (pf [(pos, pos''), (descr, descr)]) q
                    qp <- PropVector <$> proj [(posold, pos), (posnew, pos'')] q
                    return $ TupleVector [qr, qp]

combineVec :: Graph Plan -> Graph Plan -> Graph Plan -> Graph Plan
combineVec eb e1 e2 = do
                        (rf, q1, q2, pf) <- determineResultVector' e1 e2
                        (ValueVector qb) <- eb
                        d1 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ select item1 qb
                        d2 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ selectM resCol $ notC resCol item1 qb
                        q <- eqJoinM pos' posold (return d1) (proj (pf [(posold, pos), (descr, descr)]) q1) `unionM` eqJoinM pos' posold (return d2) (proj (pf [(posold, pos), (descr, descr)]) q2)
                        qr <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                        qp1 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d1
                        qp2 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d2
                        return $ TupleVector [qr, qp1, qp2]
                        
bPermuteVec :: Graph Plan -> Graph Plan -> Graph Plan
bPermuteVec e1 e2 = do
                     (rf, q1, pf) <- determineResultVector e1
                     (ValueVector q2) <- e2
                     q <- eqJoinM pos pos' (return q1) $ proj [(pos', pos), (posnew, item1)] q2
                     qr <- rf <$> proj (pf [(descr, descr), (pos, posnew)]) q
                     qp <- PropVector <$> proj [(posold, pos), (posnew, posnew)] q
                     return $ TupleVector [qr, qp]

determineResultVector :: Graph Plan -> Graph (AlgNode -> Plan, AlgNode, ProjInf -> ProjInf)
determineResultVector e = do
                            hasI <- isValueVector e
                            e' <- e
                            let rf = if hasI then ValueVector else DescrVector
                            let pf = if hasI then \x -> (item1, item1):x else \x -> x
                            let q = if hasI
                                        then let (ValueVector q') = e' in q'
                                        else let (DescrVector q') = e' in q'
                            return (rf, q, pf)

determineResultVector' :: Graph Plan -> Graph Plan -> Graph (AlgNode -> Plan, AlgNode, AlgNode, ProjInf -> ProjInf)
determineResultVector' e1 e2 = do
                                hasI <- isValueVector e1
                                e1' <- e1
                                e2' <- e2
                                let rf = if hasI then ValueVector else DescrVector
                                let pf = if hasI then \x -> (item1, item1):x else \x -> x
                                let (q1, q2) = if hasI
                                                then let (ValueVector q1') = e1'
                                                         (ValueVector q2') = e2' in (q1', q2')
                                                else let (DescrVector q1') = e1' 
                                                         (DescrVector q2') = e2' in (q1', q2')
                                return (rf, q1, q2, pf)

toDescr :: Graph Plan -> Graph Plan
toDescr v = do
             v' <- v
             case v' of
                 (DescrVector _) -> v
                 (ValueVector n) -> DescrVector <$> tagM "toDescr" (proj [(descr, descr), (pos, pos)] n)
                                        
                 _               -> error "toDescr: Cannot cast into descriptor vector"


isValueVector :: Graph Plan -> Graph Bool
isValueVector p = do
                    p' <- p
                    case p' of
                        (ValueVector _) -> return True
                        _               -> return False

-- | Construct a name that represents a lifted variable in the environment.                        
constrEnvName :: String -> Int -> String
constrEnvName x 0 = x
constrEnvName x i = x ++ "<%>" ++ show i

intFromVal :: Expr T.VType -> Int
intFromVal (Const _ (Int i)) = i
intFromVal x                 = error $ "intFromVal: not an integer: " ++ show x

tagVector :: String -> Graph Plan -> Graph Plan
tagVector s g = do
                g' <- g
                case g' of
                    (TupleVector vs) -> TupleVector <$> (sequence $ map (\v -> tagVector s (pure v)) vs)
                    (DescrVector q) -> DescrVector <$> tag s q
                    (ValueVector q) -> ValueVector <$> tag s q
                    (PrimVal q) -> PrimVal <$> tag s q
                    (NestedVector q qs) -> NestedVector <$> tag s q <*> tagVector s (return qs)
                    (PropVector q) -> PropVector <$> tag s q

