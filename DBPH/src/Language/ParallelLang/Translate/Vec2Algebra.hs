{-# LANGUAGE TemplateHaskell, RelaxedPolyRec, TupleSections #-}
module Language.ParallelLang.Translate.Vec2Algebra (toPFAlgebra, toXML, toX100Algebra, toX100String, toX100File) where

-- FIXME this should import a module from TableAlgebra which defines 
-- common types like schema info and abstract column types.
import Database.Algebra.Pathfinder(PFAlgebra)

import Database.Algebra.X100.Data(X100Algebra)
import Database.Algebra.X100.Data.Create(dummy)
import Database.Algebra.X100.JSON
import Database.Algebra.X100.Render

import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.VL.PathfinderVectorPrimitives()
import Language.ParallelLang.VL.X100VectorPrimitives()
import Database.Algebra.Dag.Common hiding (BinOp)
import Database.Algebra.Dag.Builder
import Language.ParallelLang.FKL.Data.FKL
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.VL.Data.Vector hiding (Pair)
import qualified Language.ParallelLang.VL.Data.Vector as Vec
import Language.ParallelLang.VL.Data.DBVector
import qualified Language.ParallelLang.VL.Data.Vector as Vec
import Database.Algebra.Pathfinder.Render.XML hiding (XML, Graph)
import qualified Language.ParallelLang.Common.Data.Type as T
import qualified Language.ParallelLang.Common.Data.Val as V
import Language.ParallelLang.VL.VectorOperations

import Database.Algebra.Pathfinder(initLoop)

import qualified Data.Map as M
import Control.Monad (liftM, liftM2, liftM3)
import Control.Applicative hiding (Const)

import Language.ParallelLang.Common.Impossible

import System.IO.Unsafe

fkl2Alg :: (VectorAlgebra a) => Expr -> Graph a Plan
-- fkl2Alg (Table _ n cs ks) = tableRef n cs ks
--FIXME
fkl2Alg (Const t v) = constructLiteral t v
fkl2Alg (BinOp _ (Op Cons False) e1 e2) = do {e1' <- fkl2Alg e1; e2' <- fkl2Alg e2; cons e1' e2'}
fkl2Alg (BinOp _ (Op Cons True)  e1 e2) = do {e1' <- fkl2Alg e1; e2' <- fkl2Alg e2; consLift e1' e2'}
fkl2Alg (BinOp _ (Op o False) e1 e2)    = do {(PrimVal lyt p1) <- fkl2Alg e1; (PrimVal _ p2) <- fkl2Alg e2; (DBP p _) <- binOp o (DBP p1 [1]) (DBP p2 [1]); return $ PrimVal lyt p}
fkl2Alg (BinOp _ (Op o True) e1 e2)     = do {(ValueVector lyt p1) <- fkl2Alg e1; (ValueVector _ p2) <- fkl2Alg e2; (DBV p _) <- binOpL o (DBV p1 [1]) (DBV p2 [1]); return $ ValueVector lyt p} 
{-fkl2Alg (If _ eb e1 e2) = do 
                          eb' <- fkl2Alg eb
                          e1' <- fkl2Alg e1
                          e2' <- fkl2Alg e2
                          ifList eb' e1' e2' -}
fkl2Alg (PApp1 t f arg) = fkl2Alg arg >>= case f of
                                           (LengthPrim _) -> lengthV 
                                           (LengthLift _) -> lengthLift
                                           (ConcatLift _) -> concatLift
                                           (Sum _) -> sumPrim t
                                           (SumL _) -> sumLift
                                           (The _) -> the
                                           (TheL _) -> theL
                                           (NotPrim _) -> (\(PrimVal lyt v) -> (\(DBP v' _) -> PrimVal lyt v') <$> notPrim (DBP v [1]))
                                           (NotVec _) -> (\(ValueVector lyt v) -> (\(DBV v' _) -> ValueVector lyt v') <$> notVec (DBV v [1]))
                                           (Fst _) -> fstA
                                           (Snd _) -> sndA
                                           (FstL _) -> fstL
                                           (SndL _) -> sndL
                                           (Concat _) -> concatV

fkl2Alg (PApp2 _ f arg1 arg2) = liftM2 (,) (fkl2Alg arg1) (fkl2Alg arg2) >>= uncurry fn
    where
        fn = case f of
                (Dist _) -> \x y -> dist x y
                {-(Dist_L _) -> distL
                (GroupWithS _) -> groupByS
                (GroupWithL _) -> groupByL
                (SortWithS _) -> sortWithS
                (SortWithL _) -> sortWithL
                (Index _) -> error "Index is not yet defined fkl2Alg"
                (Restrict _) -> restrict
                (BPermute _) -> bPermute
                (Unconcat _) -> unconcatV -}
                (Pair _) -> error "Pair"-- \e1 e2 -> return $ PairVector e1 e2
                (PairL _) -> error "PairL"-- \e1 e2 -> return $ PairVector e1 e2
                e -> error $ "Not supported yet: " ++ show e
-- fkl2Alg (PApp3 _ (Combine _) arg1 arg2 arg3) = liftM3 (,,) (fkl2Alg arg1) (fkl2Alg arg2) (fkl2Alg arg3) >>= (\(x, y, z) -> combine x y z)
fkl2Alg (Var _ s) = fromGam s
fkl2Alg (Clo _ n fvs x f1 f2) = do
                                fv <- constructClosureEnv fvs
                                return $ Closure n fv x f1 f2
fkl2Alg (AClo _ n fvs x f1 f2) = do
                              v <- fromGam n
                              fv <- constructClosureEnv fvs
                              return $ AClosure n v 1 fv x f1 f2 
fkl2Alg (CloApp _ c arg) = do
                             (Closure _ fvs x f1 _) <- fkl2Alg c
                             arg' <- fkl2Alg arg
                             withContext ((x, arg'):fvs) undefined $ fkl2Alg f1
fkl2Alg (CloLApp _ c arg) = do
                              (AClosure n v 1 fvs x _ f2) <- fkl2Alg c
                              arg' <- fkl2Alg arg
                              withContext ((n, v):(x, arg'):fvs) undefined $ fkl2Alg f2 

constructClosureEnv :: [String] -> Graph a [(String, Plan)]
constructClosureEnv [] = return []
constructClosureEnv (x:xs) = liftM2 (:) (liftM (x,) $ fromGam x) (constructClosureEnv xs)

toPFAlgebra :: Expr -> AlgPlan PFAlgebra Plan
toPFAlgebra e = runGraph initLoop (fkl2Alg e)

toX100Algebra :: Expr -> AlgPlan X100Algebra Plan
toX100Algebra e = runGraph dummy (fkl2Alg e)

toX100File :: FilePath -> AlgPlan X100Algebra Plan -> IO ()
toX100File f (m, r, t) = do
    planToFile f (t, rootNodes r, reverseAlgMap m)
  where
      rootNodes :: Plan -> [AlgNode]
      rootNodes (ValueVector lyt n) = n : rootNodes' lyt
      rootNodes (PrimVal lyt n) = n : rootNodes' lyt
      rootNodes (Closure _ _ _ _ _) = error "Functions cannot appear as a result value"
      rootNodes (AClosure _ _ _ _ _ _ _) = error "Function cannot appear as a result value"
      rootNodes' :: Layout AlgNode -> [AlgNode]
      rootNodes' (Vec.Pair p1 p2) = rootNodes' p1 ++ rootNodes' p2
      rootNodes' (InColumn _) = []
      rootNodes' (Nest q lyt) = q : rootNodes' lyt
      
toX100String :: AlgPlan X100Algebra Plan -> Query X100
toX100String (m, r, t) = convertQuery r
 where
    m' :: M.Map AlgNode X100Algebra
    m' = reverseAlgMap m
    convertQuery :: Plan -> Query X100
    convertQuery (PrimVal l r') = PrimVal (convertLayout l) $ X100 r' $ generateDumbQuery m' r'
    convertQuery (ValueVector l r') = ValueVector (convertLayout l) $ X100 r' $ generateDumbQuery m' r'
    convertQuery (Closure _ _ _ _ _) = error "Functions cannot appear as a result value"
    convertQuery (AClosure _ _ _ _ _ _ _) = error "Function cannot appear as a result value"
    convertLayout :: Layout AlgNode -> Layout X100
    convertLayout (InColumn i) = InColumn i
    convertLayout (Nest r' l) = Nest (X100 r' $ generateDumbQuery m' r') $ convertLayout l
    convertLayout (Vec.Pair p1 p2) = Vec.Pair (convertLayout p1) (convertLayout p2)
    
toXML :: AlgPlan PFAlgebra Plan -> Query XML
toXML = undefined
{-
toXML (g, r, ts) = case r of
                     (PrimVal r') -> PrimVal (XML r' $ toXML' withItem r')
                     (PairVector e1 e2)   -> PairVector (toXML (g, e1, ts)) (toXML (g, e2, ts))
                     (DescrVector r') -> DescrVector (XML r' $ toXML' withoutItem r')
                     (ValueVector r') -> ValueVector (XML r' $ toXML' withItem r')
                     (NestedVector r' rs) -> NestedVector (XML r' $ toXML' withoutItem r') $ toXML (g, rs, ts)
                     (Closure _ _ _ _ _) -> error "Functions cannot appear as a result value"
                     (AClosure _ _ _ _ _ _ _) -> error "Function cannot appear as a result value"
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
    

-}
