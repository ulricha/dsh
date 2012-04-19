{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.VL.VectorOperations where

import Language.ParallelLang.Common.Impossible

import Language.ParallelLang.VL.Data.GraphVector
import Language.ParallelLang.VL.Data.DBVector
import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.VL.MetaPrimitives
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Type hiding (Pair)
import qualified Language.ParallelLang.Common.Data.Type as T
import qualified Language.ParallelLang.Common.Data.Val as V
import Language.ParallelLang.FKL.Data.FKL (TypedColumn, Key)

import Control.Applicative

the :: VectorAlgebra a => Plan -> Graph a Plan
the (ValueVector d lyt@(Nest _ _)) = do
                                     p <- constructLiteralValue [intT] [PNat 1, PNat 1, PInt 1]
                                     (_, prop) <- selectPos d Eq p
                                     (Nest q' lyt') <- chainRenameFilter prop lyt
                                     return $ ValueVector q' lyt'
the (ValueVector d lyt) = do
                            p <- constructLiteralValue [intT] [PNat 1, PNat 1, PInt 1]
                            (DBV q' cols, prop) <- selectPos d Eq p
                            lyt' <- chainRenameFilter prop lyt
                            return $ PrimVal (DBP q' cols) lyt'
the _ = error "the: Should not be possible"


theL :: VectorAlgebra a => Plan -> Graph a Plan
theL (ValueVector d (Nest q lyt)) = do
                                      one <- constructLiteralValue [intT] [PNat 1, PNat 1, PInt 1]
                                      (p, _) <- distPrim one =<< toDescr d
                                      (v, p2) <- selectPosLift q Eq p 
                                      prop <- descToRename =<< toDescr d
                                      lyt' <- chainRenameFilter p2 lyt
                                      (v', _) <- propFilter prop v
                                      return $ ValueVector v' lyt'
theL _ = error "theL: Should not be possible" 

sortWithS :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
sortWithS (ValueVector q1 _) (ValueVector q2 lyt2) = do
                                   (v, p) <- sortWith q1 q2
                                   lyt2' <- chainReorder p lyt2
                                   return $ ValueVector v lyt2'
sortWithS _e1 _e2 = error "sortWithS: Should not be possible" 

sortWithL :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
sortWithL (ValueVector _ (Nest v1 _)) (ValueVector d2 (Nest v2 lyt2)) = do
                                  (v, p) <- sortWith v1 v2
                                  lyt2' <- chainReorder p lyt2
                                  return $ ValueVector d2 (Nest v lyt2')
sortWithL _ _ = error "sortWithL: Should not be possible"

-- move a descriptor from e1 to e2
unconcatV :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
unconcatV (ValueVector d1 _) (ValueVector d2 lyt2) = do
                                                         (DescrVector d') <- toDescr d1
                                                         return $ ValueVector (DBV d' []) (Nest d2 lyt2)
unconcatV _ _ = $impossible

groupByS :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
groupByS (ValueVector q1 _) (ValueVector q2 lyt2) = do
                                            (DescrVector d, v, p) <- groupBy q1 q2
                                            lyt2' <- chainReorder p lyt2
                                            return $ ValueVector (DBV d []) (Nest v lyt2')
groupByS _e1 _e2 = error $ "groupByS: Should not be possible "

groupByL :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
groupByL (ValueVector _ (Nest v1 _)) (ValueVector d2 (Nest v2 lyt2)) = do
                                        (DescrVector d, v, p) <- groupBy v1 v2
                                        lyt2' <- chainReorder p lyt2
                                        return $ ValueVector d2 (Nest (DBV d []) (Nest v lyt2'))
groupByL _ _ = error "groupByL: Should not be possible"

concatLift :: VectorAlgebra a => Plan -> Graph a Plan
concatLift (ValueVector d (Nest d' vs)) = do
                                                    p <- descToRename =<< (toDescr d')
                                                    vs' <- renameOuter' p vs
                                                    return $ ValueVector d vs'
concatLift _ = error "concatLift: Should not be possible"

lengthLift :: VectorAlgebra a => Plan -> Graph a Plan
lengthLift (ValueVector q (Nest qi _)) = do
                                            d <- toDescr q
                                            di <- toDescr qi
                                            ls <- lengthSeg d di
                                            p <- descToRename d
                                            r <- propRename p ls
                                            return $ ValueVector r (InColumn 1)
lengthLift _ = $impossible

lengthV :: VectorAlgebra a => Plan -> Graph a Plan
lengthV q = do
             v' <- outer q
             v <- lengthA v'
             return $ PrimVal v (InColumn 1)

cons :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
cons q1@(PrimVal _ _) q2@(ValueVector _ _) = do
                                             n <- singletonPrim q1
                                             appendR n q2
cons q1 q2 = do
                n <- singletonVec q1
                appendR n q2

consLift :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
consLift (ValueVector q1 lyt1) (ValueVector q2 (Nest qi lyt2)) = do
                        s <- segment q1
                        (v, p1, p2) <- append s qi
                        lyt1' <- renameOuter' p1 lyt1
                        lyt2' <- renameOuter' p2 lyt2
                        lyt' <- appendR' lyt1' lyt2'
                        return $ ValueVector q2 (Nest v lyt')
consLift _ _ = $impossible
                        

restrict :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
restrict(ValueVector q1 lyt) (ValueVector q2 (InColumn 1))
                  = do
                      (v, p) <- restrictVec q1 q2
                      lyt' <- chainRenameFilter p lyt
                      return $ ValueVector v lyt'
restrict (AClosure n l i env arg e1 e2) bs = do
                                            l' <- restrict l bs
                                            env' <- mapEnv (flip restrict bs) env
                                            return $ AClosure n l' i env' arg e1 e2 
restrict e1 e2 = error $ "restrict: Can't construct restrict node " ++ show e1 ++ " " ++ show e2

combine :: VectorAlgebra a => Plan -> Plan -> Plan -> Graph a Plan
combine (ValueVector qb (InColumn 1)) (ValueVector q1 lyt1) (ValueVector q2 lyt2) =
                      do
                        (v, p1, p2) <- combineVec qb q1 q2
                        lyt1' <- renameOuter' p1 lyt1
                        lyt2' <- renameOuter' p2 lyt2
                        lyt' <- appendR' lyt1' lyt2'
                        return $ ValueVector v lyt'
combine _ _ _ = $impossible


outer :: VectorAlgebra a => Plan -> Graph a DescrVector
outer (PrimVal _ _) = $impossible
outer (ValueVector q _) = toDescr q
outer (Closure _ _ _ _ _) = $impossible
outer (AClosure _ v _ _ _ _ _) = outer v

dist :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
dist (PrimVal q lyt) q2 = do
                           o <- outer q2
                           (v, p) <- distPrim q o
                           lyt' <- chainReorder p lyt
                           return $ ValueVector v lyt'
dist (ValueVector q lyt) q2 = do
                               o@(DescrVector qo) <- outer q2
                               (d, p) <- distDesc q o
                               lyt' <- chainReorder p lyt
                               return $ ValueVector (DBV qo []) (Nest d lyt')
dist (Closure n env x f fl) q2 = (\env' -> AClosure n q2 1 env' x f fl) <$> mapEnv (flip dist q2) env
dist _ _ = $impossible

mapEnv :: VectorAlgebra a => (Plan -> Graph a Plan) -> [(String, Plan)] -> Graph a [(String, Plan)]
mapEnv f  ((x, p):xs) = (\p' xs' -> (x, p'):xs') <$> f p <*> mapEnv f xs
mapEnv _f []          = return []

sumPrim :: VectorAlgebra a => Type -> Plan -> Graph a Plan
sumPrim t (ValueVector q (InColumn 1)) = flip PrimVal (InColumn 1) <$> vecSum t q
sumPrim _ _ = $impossible

sumLift :: VectorAlgebra a =>  Plan -> Graph a Plan
sumLift (ValueVector d1 (Nest q (InColumn 1))) = do
                                                  d <- toDescr d1
                                                  flip ValueVector (InColumn 1) <$> vecSumLift d q
sumLift _ = $impossible


distL :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
distL (ValueVector q1 lyt1) (ValueVector d (Nest o _)) = do
                                                          (v, p) <- distLift q1 =<< toDescr o
                                                          lyt1' <- chainReorder p lyt1
                                                          return $ ValueVector d (Nest v lyt1')
distL (AClosure n v i xs x f fl) q2 = do
                                        v' <- distL v q2
                                        xs' <- mapEnv (\y -> distL y v') xs
                                        return $ AClosure n v' (i + 1) xs' x f fl
distL _e1 _e2 = error $ "distL: Should not be possible" ++ show _e1 ++ "\n" ++ show _e2


ifList :: VectorAlgebra a => Plan -> Plan -> Plan -> Graph a Plan
ifList (PrimVal qb _) (ValueVector q1 lyt1) (ValueVector q2 lyt2) =
    do
     (d1', _) <- distPrim qb =<< toDescr q1
     (d1, p1) <- restrictVec q1 d1'
     qb' <- notPrim qb
     (d2', _) <- distPrim qb' =<< toDescr q2
     (d2, p2) <- restrictVec q2 d2'
     r1 <- renameOuter' p1 lyt1
     r2 <- renameOuter' p2 lyt2
     lyt' <- appendR' r1 r2
     (d, _, _) <- append d1 d2
     return $ ValueVector d lyt'
ifList qb (PrimVal (DBP q1 cols1) lyt1) (PrimVal (DBP q2 cols2) lyt2) = do
                                                   (ValueVector (DBV q cols) lyt) <- ifList qb (ValueVector (DBV q1 cols1) lyt1) (ValueVector (DBV q2 cols2) lyt2)
                                                   return $ PrimVal (DBP q cols) lyt
ifList _ _ _ = $impossible

zipOpL :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
zipOpL (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
                                                     q <- zipL q1 q2
                                                     let lyt = zipLayout lyt1 lyt2
                                                     return $ ValueVector q lyt
zipOpL _ _ = $impossible

zipOp :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
zipOp (PrimVal q1 lyt1) (PrimVal q2 lyt2) = do
                                             q <- zipA q1 q2
                                             let lyt = zipLayout lyt1 lyt2
                                             return $ PrimVal q lyt
zipOp (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
                                                    d <- constructLiteralValue [] [PNat 1, PNat 1]
                                                    let lyt = zipLayout (Nest q1 lyt1) (Nest q2 lyt2)
                                                    return $ PrimVal d lyt
zipOp (ValueVector q1 lyt1) (PrimVal q2 lyt2) = do
                                                 let lyt = zipLayout (Nest q1 lyt1) lyt2
                                                 return $ PrimVal q2 lyt
zipOp (PrimVal q1 lyt1) (ValueVector q2 lyt2) = do
                                                 let lyt = zipLayout lyt1 (Nest q2 lyt2)
                                                 return $ PrimVal q1 lyt
zipOp _ _ = $impossible

fstA :: VectorAlgebra a => Plan -> Graph a Plan   
fstA (PrimVal _q (Pair (Nest q lyt) _p2)) = return $ ValueVector q lyt
fstA (PrimVal q (Pair p1 _p2)) = do
                                     let (p1', cols) = projectFromPos p1
                                     proj <- projectA q cols
                                     return $ PrimVal proj p1'
fstA e1 = error $ "fstA: " ++ show e1                                                     

fstL :: VectorAlgebra a => Plan -> Graph a Plan   
fstL (ValueVector q (Pair p1 _p2)) = do
                                        let(p1', cols) = projectFromPos p1
                                        proj <- projectL q cols
                                        return $ ValueVector proj p1'
fstL _ = $impossible

sndA :: VectorAlgebra a => Plan -> Graph a Plan   
sndA (PrimVal _q (Pair _p1 (Nest q lyt))) = return $ ValueVector q lyt
sndA (PrimVal q (Pair _p1 p2)) = do
                                    let (p2', cols) = projectFromPos p2
                                    proj <- projectA q cols
                                    return $ PrimVal proj p2'
sndA _ = $impossible
    
sndL :: VectorAlgebra a => Plan -> Graph a Plan   
sndL (ValueVector q (Pair _p1 p2)) = do
                                        let (p2', cols) = projectFromPos p2
                                        proj <- projectL q cols
                                        return $ ValueVector proj p2'
sndL _ = $impossible

projectFromPos :: Layout -> (Layout, [DBCol])
projectFromPos = (\(x,y,_) -> (x,y)) . (projectFromPosWork 1)
    where
      projectFromPosWork :: Int -> Layout -> (Layout, [DBCol], Int)
      projectFromPosWork c (InColumn i)   = (InColumn c, [i], c + 1)
      projectFromPosWork c (Nest q l)       = (Nest q l, [], c)
      projectFromPosWork c (Pair p1 p2)   = let (p1', cols1, c') = projectFromPosWork c p1
                                                (p2', cols2, c'') = projectFromPosWork c' p2
                                             in (Pair p1' p2', cols1 ++ cols2, c'')
                                             
concatV :: Plan -> Graph a Plan
concatV (ValueVector _ (Nest q lyt)) = return $ ValueVector q lyt
concatV (AClosure n v l fvs x f1 f2) | l > 1 = AClosure n <$> (concatV v) 
                                                          <*> pure (l - 1) 
                                                          <*> (mapM (\(y, val) -> do
                                                                                     val' <- concatV val
                                                                                     return (y, val')) fvs)
                                                          <*> pure x <*> pure f1 <*> pure f2
concatV e                  = error $ "Not supported by concatV: " ++ show e


singletonVec :: VectorAlgebra a => Plan -> Graph a Plan
singletonVec (ValueVector q lyt) = do
                                 (DescrVector d) <- singletonDescr
                                 return $ ValueVector (DBV d []) (Nest q lyt)
singletonVec _ = error "singletonVec: Should not be possible"

singletonPrim :: VectorAlgebra a => Plan -> Graph a Plan
singletonPrim (PrimVal (DBP q1 cols) lyt) = return $ ValueVector (DBV q1 cols) lyt
singletonPrim _ = error "singletonPrim: Should not be possible"

dbTable :: VectorAlgebra a => String -> [TypedColumn] -> [Key] -> Graph a Plan
dbTable n cs ks = do
                    t <- tableRef n cs ks
                    return $ ValueVector t (foldr1 Pair [InColumn i | i <- [1..length cs]])

mkLiteral :: VectorAlgebra a => Type -> V.Val -> Graph a Plan                    
mkLiteral t@(List _) (V.List es) = do
                                            ((descHd, descV), layout, _) <- toPlan (mkDescriptor [length es]) t 1 es
                                            (flip ValueVector layout) <$> (constructLiteralTable (reverse descHd) $ map reverse descV) 
mkLiteral (Fn _ _) _ = error "Not supported"
mkLiteral t e           = do
                            ((descHd, [descV]), layout, _) <- toPlan (mkDescriptor [1]) (List t) 1 [e]
                            flip PrimVal layout <$> constructLiteralValue (reverse descHd) (reverse descV)
                            
type Table = ([Type], [[PVal]])

toPlan :: VectorAlgebra a => Table -> Type -> Int -> [V.Val] -> Graph a (Table, Layout, Int)
toPlan (descHd, descV) (List t) c es = case t of
                                             (T.Pair t1 t2) -> do 
                                                                 let (e1s, e2s) = unzip $ map splitVal es
                                                                 (desc', l1, c') <- toPlan (descHd, descV) (List t1) c e1s
                                                                 (desc'', l2, c'') <- toPlan desc' (List t2) c' e2s
                                                                 return (desc'', Pair l1 l2, c'')
                                             (List _) -> do
                                                              let vs = map fromListVal es
                                                              let d = mkDescriptor $ map length vs
                                                              ((hd, vs'), l, _) <- toPlan d t 1 (concat vs)
                                                              n <- constructLiteralTable (reverse hd) (map reverse vs')
                                                              return ((descHd, descV), Nest n l, c)
                                                                 
                                             (Fn _ _) -> error "Function are not db values"
                                             _ -> let (hd, vs) = mkColumn t es
                                                   in return ((hd:descHd, zipWith (:) vs descV), (InColumn c), c + 1)
toPlan _ (Fn _ _) _ _ = $impossible
toPlan (descHd, descV) t c v = let (hd, v') = mkColumn t v
                              in return $ ((hd:descHd, zipWith (:) v' descV), (InColumn c), c + 1)

fromListVal :: V.Val -> [V.Val]
fromListVal (V.List es) = es
fromListVal _              = error "fromListVal: Not a list"

splitVal :: V.Val -> (V.Val, V.Val)
splitVal (V.Pair e1 e2) = (e1, e2)
splitVal _                 = error $ "splitVal: Not a tuple" 


pVal :: V.Val -> PVal
pVal (V.Int i) = PInt i
pVal (V.Bool b) = PBool b
pVal (V.String s) = PString s
pVal (V.Double d) = PDouble d
pVal V.Unit = PUnit
pVal _ = error "pVal: Not a supported value"

mkColumn :: Type -> [V.Val] -> (Type, [PVal])
mkColumn t vs = (t, [pVal v | v <- vs]) 
                                            
mkDescriptor :: [Int] -> Table
mkDescriptor lengths = let header = []
                           body = map (\(d, p) -> [PNat $ fromIntegral p, PNat $ fromIntegral d]) $ zip (concat [ replicate l p | (p, l) <- zip [1..] lengths] ) [1..]
                        in (header, body)