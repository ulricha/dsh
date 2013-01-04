{-# LANGUAGE RelaxedPolyRec  #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}
module Database.DSH.Flattening.Translate.FKL2VL (specializeVectorOps, toVec, toVecDot, toVecJSON) where

import qualified Database.Algebra.Dag                          as Dag
import           Database.Algebra.Dag.Builder
import           Database.Algebra.VL.Data                      (VL())
import           Database.Algebra.VL.Render.Dot
import           Database.Algebra.VL.Render.JSON               ()
import           Database.DSH.Flattening.Common.Data.Op
import qualified Database.DSH.Flattening.Common.Data.QueryPlan as QP
import           Database.DSH.Flattening.Common.Data.Type      (Type())
import           Database.DSH.Flattening.Common.Data.Val       (Val())
import           Database.DSH.Flattening.FKL.Data.FKL
import           Database.DSH.Flattening.VL.Data.DBVector
import           Database.DSH.Flattening.VL.Data.GraphVector   hiding (Pair)
import           Database.DSH.Flattening.VL.VLPrimitives
import           Database.DSH.Flattening.VL.VectorOperations

import           Control.Applicative                           hiding (Const)
import           Control.Monad                                 (liftM, liftM2, liftM3)
import           Data.Aeson                                    (FromJSON, ToJSON, encode)
import           Data.ByteString.Lazy.Char8                    (unpack)
import qualified Data.IntMap                                   as M

fkl2VL :: Expr -> Graph VL Shape
fkl2VL (Table _ n cs ks) = dbTable n cs ks
fkl2VL (Const t v) = mkLiteral t v
fkl2VL (BinOp _ (Op Cons False) e1 e2) = do {e1' <- fkl2VL e1; e2' <- fkl2VL e2; cons e1' e2'}
fkl2VL (BinOp _ (Op Cons True)  e1 e2) = do {e1' <- fkl2VL e1; e2' <- fkl2VL e2; consLift e1' e2'}
fkl2VL (BinOp _ (Op o False) e1 e2)    = do {(PrimVal p1 lyt) <- fkl2VL e1; (PrimVal p2 _) <- fkl2VL e2; p <- compExpr2 o p1 p2; return $ PrimVal p lyt}
fkl2VL (BinOp _ (Op o True) e1 e2)     = do {(ValueVector p1 lyt) <- fkl2VL e1; (ValueVector p2 _) <- fkl2VL e2; p <- compExpr2L o p1 p2; return $ ValueVector p lyt}
fkl2VL (If _ eb e1 e2) = do
                          eb' <- fkl2VL eb
                          e1' <- fkl2VL e1
                          e2' <- fkl2VL e2
                          ifList eb' e1' e2'
fkl2VL (PApp1 t f arg) = fkl2VL arg >>= case f of
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
                                           (QuickConcat _) -> quickConcatV
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
fkl2VL (PApp2 _ f arg1 arg2) = liftM2 (,) (fkl2VL arg1) (fkl2VL arg2) >>= uncurry fn
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
fkl2VL (PApp3 _ (Combine _) arg1 arg2 arg3) = liftM3 (,,) (fkl2VL arg1) (fkl2VL arg2) (fkl2VL arg3) >>= (\(x, y, z) -> combine x y z)
fkl2VL (Var _ s) = fromGam s
fkl2VL (Clo _ n fvs x f1 f2) = do
                                fv <- constructClosureEnv fvs
                                return $ Closure n fv x f1 f2
fkl2VL (AClo _ n fvs x f1 f2) = do
                              v <- fromGam n
                              fv <- constructClosureEnv fvs
                              return $ AClosure n v 1 fv x f1 f2
fkl2VL (CloApp _ c arg) = do
                             (Closure _ fvs x f1 _) <- fkl2VL c
                             arg' <- fkl2VL arg
                             withContext ((x, arg'):fvs) undefined $ fkl2VL f1
fkl2VL (CloLApp _ c arg) = do
                              (AClosure n v 1 fvs x _ f2) <- fkl2VL c
                              arg' <- fkl2VL arg
                              withContext ((n, v):(x, arg'):fvs) undefined $ fkl2VL f2

constructClosureEnv :: [String] -> Graph a [(String, Shape)]
constructClosureEnv [] = return []
constructClosureEnv (x:xs) = liftM2 (:) (liftM (x,) $ fromGam x) (constructClosureEnv xs)

toVec :: Expr -> AlgPlan VL Shape
toVec e = runGraph emptyVL (fkl2VL e)

specializeVectorOps :: Expr -> QP.QueryPlan VL
specializeVectorOps e =
  let (opMap, shape, tagMap) = runGraph emptyVL (fkl2VL e)

      topShape               = QP.exportShape shape
      rs                     = QP.rootsFromTopShape topShape
      d                      = Dag.mkDag (reverseAlgMap opMap) rs
  in QP.QueryPlan { QP.queryDag = d, QP.queryShape = topShape, QP.queryTags = tagMap }

toVecDot :: Expr -> String
toVecDot e = let (gr,p,ts) = toVec e
             in renderVLDot ts (rootNodes p) (reverseAlgMap gr)

toVecJSON :: Expr -> String
toVecJSON e = let (gr,p, _) = toVec e
               in unpack $ encode (p, M.toList $ reverseAlgMap gr)

instance ToJSON Shape where
instance ToJSON DBV where
instance ToJSON DBP where
instance ToJSON Layout where
instance ToJSON Expr where
instance ToJSON Prim1 where
instance ToJSON Prim2 where
instance ToJSON Prim3 where
instance ToJSON Oper where
instance ToJSON Op where
instance ToJSON Type where
instance ToJSON Val where

instance FromJSON Shape where
instance FromJSON DBV where
instance FromJSON DBP where
instance FromJSON Layout where
instance FromJSON Expr where
instance FromJSON Prim1 where
instance FromJSON Prim2 where
instance FromJSON Prim3 where
instance FromJSON Oper where
instance FromJSON Op where
instance FromJSON Type where
instance FromJSON Val where

