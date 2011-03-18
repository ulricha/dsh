module Language.ParallelLang.Translate.Vec2Algebra where

import Database.Ferry.Algebra hiding (getLoop, withContext, Gam)
import qualified Database.Ferry.Algebra as A

import Control.Applicative
type Graph = GraphM Plan


type Gam = A.Gam Plan

data Plan =
         Tuple [Plan]
       | DescrVector AlgNode
       | ValueVector AlgNode
       | PrimVal AlgNode
       | NestedVector AlgNode Plan
       | PropVector AlgNode
       
-- | Results are stored in column:
pos, item1, descr, descr', descr'', pos', pos'', pos''', posold, posnew, ordCol, resCol :: String
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


outer :: Graph Plan -> Graph Plan
outer e = do
            e' <- e
            case e' of
                NestedVector p _  -> return $ DescrVector p
                -- v@(ValueVector _) -> return $ v
                _                 -> error "outer: Can't extract outer plan"
                
distPrim :: Graph Plan -> Graph Plan -> Graph Plan
distPrim v d = do
                 (PrimVal q1) <- v
                 (DescrVector q2) <- toDescr d
                 DescrVector <$> crossM (proj [(item1, item1)] q1) (return q2)
                  
distDesc :: Graph Plan -> Graph Plan -> Graph Plan
distDesc e1 e2 = do
                   hasI <- isValueVector e1
                   let rf = if hasI then ValueVector else DescrVector
                   (DescrVector q2) <- toDescr e2
                   e1' <- e1
                   let (q1, pI) = case hasI of
                                    True -> case e1' of
                                                (ValueVector q1) -> (q1, [(item1, item1)])
                                                _                -> error "distDesc: Not a value vector"
                                    False -> case e1' of
                                                (DescrVector q1) -> (q1, [])
                                                _                -> error "distDesc: Not a descriptor vector"
                   q <- projM ([(descr, pos), (pos, pos''), (posold, posold)] ++ pI) $ rownumM pos'' [pos, pos'] Nothing $ crossM (proj [(pos, pos)] q2) (proj ([(pos', pos), (posold, pos)] ++ pI) q1)
                   qr1 <- rf <$> proj ([(descr, descr), (pos, pos)] ++ pI) q
                   qr2 <- PropVector <$> proj [(posold, posold), (posnew, pos)] q
                   return $ Tuple [qr1, qr2]

distLift :: Graph Plan -> Graph Plan -> Graph Plan
distLift e1 e2 = do
                    hasI <- isValueVector e1
                    let rf = if hasI then ValueVector else DescrVector
                    (DescrVector q2) <- toDescr e2
                    e1' <- e1
                    let (q1, pI) = case hasI of
                                    True -> case e1' of
                                                (ValueVector q1) -> (q1, [(item1, item1)])
                                                _                -> error "distDesc: Not a value vector"
                                    False -> case e1' of
                                                (DescrVector q1) -> (q1, [])
                                                _                -> error "distDesc: Not a descriptor vector"
                    q <- eqJoinM pos' descr (proj ((pos', pos):pI) q1) $ return q2
                    qr1 <- rf <$> proj ([(descr, descr), (pos, pos)] ++ pI) q
                    qr2 <- DescrVector <$> proj [(posold, pos'), (posnew, pos)] q
                    return $ Tuple [qr1, qr2]                    

var :: String -> Graph Plan
var s = fromGam s


toDescr :: Graph Plan -> Graph Plan
toDescr v = do
             v' <- v
             case v' of
                 (DescrVector _) -> v
                 (ValueVector n) -> DescrVector <$> proj [(descr, descr), (pos, pos)] n
                                        
                 _               -> error "toDescr: Cannot cast into descriptor vector"

isValueVector :: Graph Plan -> Graph Bool
isValueVector p = do
                    p' <- p
                    case p' of
                        (ValueVector n) -> return True
                        _               -> return False