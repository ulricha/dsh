{-# LANGUAGE TemplateHaskell, RelaxedPolyRec, TupleSections #-}
module Language.ParallelLang.Translate.Vec2Algebra (toPFAlgebra, toXML, toX100Algebra, toX100String, toX100File, toVec, toVecDot) where

-- FIXME this should import a module from TableAlgebra which defines 
-- common types like schema info and abstract column types.
import Database.Algebra.Pathfinder(PFAlgebra)

import Database.Algebra.X100.Data(X100Algebra)
import Database.Algebra.X100.Data.Create(dummy)
import Database.Algebra.X100.JSON
import Database.Algebra.X100.Render

import Database.Algebra.Pathfinder.Render.XML hiding (XML, Graph)

import Language.ParallelLang.VL.Data.VectorLanguage(VL())
import Language.ParallelLang.VL.Render.Dot 
import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.VL.PathfinderVectorPrimitives()
import Language.ParallelLang.VL.VLPrimitives
import Language.ParallelLang.VL.X100VectorPrimitives()
import Database.Algebra.Dag.Common hiding (BinOp)
import Database.Algebra.Dag.Builder
import Language.ParallelLang.FKL.Data.FKL
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.VL.Data.GraphVector hiding (Pair)
import qualified Language.ParallelLang.VL.Data.GraphVector as Vec
import Language.ParallelLang.VL.Data.DBVector
import qualified Language.ParallelLang.VL.Data.Query as Ext
import Language.ParallelLang.VL.VectorOperations

import Database.Algebra.Pathfinder(initLoop)

import qualified Data.Map as M
import Control.Monad (liftM, liftM2, liftM3)
import Control.Applicative hiding (Const)

fkl2Alg :: (VectorAlgebra a) => Expr -> Graph a Plan
fkl2Alg (Table _ n cs ks) = dbTable n cs ks
--FIXME
fkl2Alg (Const t v) = mkLiteral t v
fkl2Alg (BinOp _ (Op Cons False) e1 e2) = do {e1' <- fkl2Alg e1; e2' <- fkl2Alg e2; cons e1' e2'}
fkl2Alg (BinOp _ (Op Cons True)  e1 e2) = do {e1' <- fkl2Alg e1; e2' <- fkl2Alg e2; consLift e1' e2'}
fkl2Alg (BinOp _ (Op o False) e1 e2)    = do {(PrimVal p1 lyt) <- fkl2Alg e1; (PrimVal p2 _) <- fkl2Alg e2; p <- binOp o p1 p2; return $ PrimVal p lyt}
fkl2Alg (BinOp _ (Op o True) e1 e2)     = do {(ValueVector p1 lyt) <- fkl2Alg e1; (ValueVector p2 _) <- fkl2Alg e2; p <- binOpL o p1 p2; return $ ValueVector p lyt} 
fkl2Alg (If _ eb e1 e2) = do 
                          eb' <- fkl2Alg eb
                          e1' <- fkl2Alg e1
                          e2' <- fkl2Alg e2
                          ifList eb' e1' e2'
fkl2Alg (PApp1 t f arg) = fkl2Alg arg >>= case f of
                                           (LengthPrim _) -> lengthV 
                                           (LengthLift _) -> lengthLift
                                           (ConcatLift _) -> concatLift
                                           (Sum _) -> sumPrim t
                                           (SumL _) -> sumLift
                                           (The _) -> the
                                           (TheL _) -> theL
                                           (NotPrim _) -> (\(PrimVal v lyt) -> (\v' -> PrimVal v' lyt) <$> notPrim v)
                                           (NotVec _) -> (\(ValueVector v lyt) -> (\v' -> ValueVector v' lyt) <$> notVec v)
                                           (Fst _) -> fstA
                                           (Snd _) -> sndA
                                           (FstL _) -> fstL
                                           (SndL _) -> sndL
                                           (Concat _) -> concatV
                                           (Minimum _) -> minPrim
                                           (MinimumL _) -> minLift
                                           (Maximum _)  -> maxPrim
                                           (MaximumL _) -> maxLift
                                           (IntegerToDouble _) -> (\(PrimVal v lyt) -> (\v' -> PrimVal v' lyt) <$> integerToDoubleA v)
                                           (IntegerToDoubleL _) -> (\(ValueVector v lyt) -> (\v' -> ValueVector v' lyt) <$> integerToDoubleL v)
                                           (Tail _) -> tailS
                                           (TailL _) -> tailL
                                           (Reverse _) -> reversePrim
                                           (ReverseL _) -> reverseLift
                                           (And _) -> andPrim
                                           (AndL _) -> andLift
                                           (Or _) -> orPrim
                                           (OrL _) -> orLift
                                           (Init _) -> initPrim
                                           (InitL _) -> initLift
                                           (Last _) -> lastPrim
                                           (LastL _) -> lastLift
                                           (Nub _) -> nubPrim
                                           (NubL _) -> nubLift
fkl2Alg (PApp2 _ f arg1 arg2) = liftM2 (,) (fkl2Alg arg1) (fkl2Alg arg2) >>= uncurry fn
    where
        fn = case f of
                (Dist _) -> \x y -> dist x y
                (Dist_L _) -> distL
                (GroupWithS _) -> groupByS
                (GroupWithL _) -> groupByL
                (SortWithS _) -> sortWithS
                (SortWithL _) -> sortWithL
                (Restrict _) -> restrict
                (Unconcat _) -> unconcatV
                (Pair _) -> pairOp
                (PairL _) -> pairOpL
                (Append _) -> appendPrim
                (AppendL _) -> appendLift
                (Index _) -> indexPrim
                (IndexL _) -> indexLift
                (Take _) -> takePrim
                (TakeL _) -> takeLift
                (Drop _) -> dropPrim
                (DropL _) -> dropLift
                (Zip _) -> zipPrim
                (ZipL _) -> zipLift
                (TakeWithS _) -> takeWithS
                (TakeWithL _) -> takeWithL
                (DropWithS _) -> dropWithS
                (DropWithL _) -> dropWithL
fkl2Alg (PApp3 _ (Combine _) arg1 arg2 arg3) = liftM3 (,,) (fkl2Alg arg1) (fkl2Alg arg2) (fkl2Alg arg3) >>= (\(x, y, z) -> combine x y z)
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

toVec :: Expr -> AlgPlan VL Plan
toVec e = runGraph emptyVL (fkl2Alg e)

toVecDot :: Expr -> String
toVecDot e = let (gr,p,ts) = toVec e
             in renderVLDot ts (rootNodes p) (reverseAlgMap gr)

toX100File :: FilePath -> AlgPlan X100Algebra Plan -> IO ()
toX100File f (m, r, t) = do
    planToFile f (t, rootNodes r, reverseAlgMap m)
      
toX100String :: AlgPlan X100Algebra Plan -> Ext.Query Ext.X100
toX100String (m, r, _t) = convertQuery r
 where
    m' :: M.Map AlgNode X100Algebra
    m' = reverseAlgMap m
    convertQuery :: Plan -> Ext.Query Ext.X100
    convertQuery (PrimVal (DBP r' _) l) = Ext.PrimVal (Ext.X100 r' $ generateDumbQuery m' r') $ convertLayout l
    convertQuery (ValueVector (DBV r' _) l) = Ext.ValueVector (Ext.X100 r' $ generateDumbQuery m' r') $ convertLayout l
    convertQuery (Closure _ _ _ _ _) = error "Functions cannot appear as a result value"
    convertQuery (AClosure _ _ _ _ _ _ _) = error "Function cannot appear as a result value"
    convertLayout :: Layout -> Ext.Layout Ext.X100
    convertLayout (InColumn i) = Ext.InColumn i
    convertLayout (Nest (DBV r' _) l) = Ext.Nest (Ext.X100 r' $ generateDumbQuery m' r') $ convertLayout l
    convertLayout (Vec.Pair p1 p2) = Ext.Pair (convertLayout p1) (convertLayout p2)
    
toXML :: AlgPlan PFAlgebra Plan -> Ext.Query Ext.XML
toXML (g, r, ts) = convertQuery r
    where
        convertQuery :: Plan -> Ext.Query Ext.XML
        convertQuery (PrimVal (DBP r' _) l) = Ext.PrimVal (Ext.XML r' $ toXML' (withItem $ columnsInLayout l) r') $ convertLayout l
        convertQuery (ValueVector (DBV r' _) l) = Ext.ValueVector (Ext.XML r' $ toXML' (withItem $ columnsInLayout l) r') $ convertLayout l
        convertQuery (Closure _ _ _ _ _) = error "Functions cannot appear as a result value"
        convertQuery (AClosure _ _ _ _ _ _ _) = error "Function cannot appear as a result value"
        convertLayout :: Layout -> Ext.Layout Ext.XML
        convertLayout (InColumn i) = Ext.InColumn i
        convertLayout (Nest (DBV r' _) l) = Ext.Nest (Ext.XML r' $ toXML' (withItem $ columnsInLayout l) r') $ convertLayout l
        convertLayout (Vec.Pair p1 p2) = Ext.Pair (convertLayout p1) (convertLayout p2)
        itemi :: Int -> Element ()
        itemi i = [attr "name" $ "item" ++ show i, attr "new" "false", attr "function" "item", attr "position" (show i)] `attrsOf` xmlElem "column"
        withItem :: Int -> [Element ()]
        withItem i = (iterCol:posCol:[ itemi i' | i' <- [1..i]])
        nodeTable = M.fromList $ map (\(a, b) -> (b, a)) $ M.toList g
        toXML' :: [Element ()] -> AlgNode -> String
        toXML' cs n = show $ document $ mkXMLDocument $ mkPlanBundle $ 
                        runXML False M.empty M.empty $
                            mkQueryPlan Nothing (xmlElem "property") $ 
                                runXML True nodeTable ts $ serializeAlgebra cs n
    

