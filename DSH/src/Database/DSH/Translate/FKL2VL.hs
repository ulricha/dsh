{-# LANGUAGE RelaxedPolyRec  #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Database.DSH.Translate.FKL2VL (specializeVectorOps) where

import           Control.Monad
       
import           Database.Algebra.Dag.Builder
import           Database.Algebra.Dag.Common(Algebra(UnOp))
import           Database.Algebra.VL.Data                      (VL(), UnOp(Project), Expr1(..))
import           Database.Algebra.VL.Render.JSON               ()
import           Database.DSH.Common.Data.Op
import qualified Database.DSH.Common.Data.QueryPlan as QP
import           Database.DSH.Common.Data.Type 
import           Database.DSH.FKL.Data.FKL
import           Database.DSH.VL.Data.GraphVector   hiding (Pair)
import           Database.DSH.VL.Data.DBVector
import           Database.DSH.VL.VLPrimitives
import           Database.DSH.VL.VectorOperations

fkl2VL :: Expr -> Graph VL Shape
fkl2VL expr =
    case expr of
        Table _ n cs ks -> dbTable n cs ks
        Const t v -> mkLiteral t v
        BinOp _ (Op Cons False) e1 e2 -> do 
            e1' <- fkl2VL e1
            e2' <- fkl2VL e2
            cons e1' e2'
        BinOp _ (Op Cons True)  e1 e2 -> do 
            e1' <- fkl2VL e1
            e2' <- fkl2VL e2
            consLift e1' e2'
        BinOp _ (Op o False) e1 e2    -> do 
            PrimVal p1 lyt <- fkl2VL e1
            PrimVal p2 _   <- fkl2VL e2
            p              <- vlBinExpr o p1 p2
            return $ PrimVal p lyt
        BinOp _ (Op o True) e1 e2     -> do 
            ValueVector p1 lyt <- fkl2VL e1
            ValueVector p2 _   <- fkl2VL e2
            p                  <- vlBinExpr o p1 p2
            return $ ValueVector p lyt
        If _ eb e1 e2 -> do
            eb' <- fkl2VL eb
            e1' <- fkl2VL e1
            e2' <- fkl2VL e2
            ifList eb' e1' e2'
        PApp1 t f arg -> do
            arg' <- fkl2VL arg 
            papp1 t f arg'
        PApp2 _ f arg1 arg2 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            papp2 f arg1' arg2'
        PApp3 _ (FCombine _) arg1 arg2 arg3 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            arg3' <- fkl2VL arg3
            combine arg1' arg2' arg3'
        Var _ s -> fromGam s
        Clo _ n fvs x f1 f2 -> do
            fv <- constructClosureEnv fvs
            return $ Closure n fv x f1 f2
        AClo _ n fvs x f1 f2 -> do
            v  <- fromGam n
            fv <- constructClosureEnv fvs
            return $ AClosure n v 1 fv x f1 f2
        CloApp _ c arg -> do
            Closure _ fvs x f1 _ <- fkl2VL c
            arg'                 <- fkl2VL arg
            withContext ((x, arg'):fvs) undefined $ fkl2VL f1
        CloLApp _ c arg -> do
            AClosure n v 1 fvs x _ f2 <- fkl2VL c
            arg'                      <- fkl2VL arg
            withContext ((n, v):(x, arg'):fvs) undefined $ fkl2VL f2

papp1 :: Type -> Prim1 -> Shape -> Graph VL Shape
papp1 t f =
    case f of
        FLength _           -> lengthV
        FLengthL _          -> lengthLift
        FConcatL _          -> concatLift
        FSum _              -> sumPrim t
        FSumL _             -> sumLift t
        FAvg _              -> avgPrim
        FAvgL _             -> avgLift
        FThe _              -> the
        FTheL _             -> theL
        FNot _              -> notS
        FNotL _             -> notL
        FFst _              -> fstA
        FSnd _              -> sndA
        FFstL _             -> fstL
        FSndL _             -> sndL
        FConcat _           -> concatV
        FQuickConcat _      -> quickConcatV
        FMinimum _          -> minPrim
        FMinimumL _         -> minLift
        FMaximum _          -> maxPrim
        FMaximumL _         -> maxLift
        FIntegerToDouble _  -> integerToDoubleS
        FIntegerToDoubleL _ -> integerToDoubleL
        FTail _             -> tailS
        FTailL _            -> tailL
        FReverse _          -> reversePrim
        FReverseL _         -> reverseLift
        FAnd _              -> andPrim
        FAndL _             -> andLift
        FOr _               -> orPrim
        FOrL _              -> orLift
        FInit _             -> initPrim
        FInitL _            -> initLift
        FLast _             -> lastPrim
        FLastL _            -> lastLift
        FNub _              -> nubPrim
        FNubL _             -> nubLift
        FNumber _           -> numberPrim
        FNumberL _          -> numberLift
        FTranspose _        -> transposePrim
        FTransposeL _       -> transposeLift
        FReshape m n _      -> reshapePrim m n
        FReshapeL m n _     -> reshapeLift m n

papp2 :: Prim2 -> Shape -> Shape -> Graph VL Shape
papp2 f =
    case f of
        FDist _            -> dist
        FDistL _           -> distL
        FGroupWithKey _    -> groupByKeyS
        FGroupWithKeyL _   -> groupByKeyL
        FSortWithS _       -> sortWithS
        FSortWithL _       -> sortWithL
        FRestrict _        -> restrict
        FUnconcat _        -> unconcatV
        FPair _            -> pairOp
        FPairL _           -> pairOpL
        FAppend _          -> appendPrim
        FAppendL _         -> appendLift
        FIndex _           -> indexPrim
        FIndexL _          -> indexLift
        FTake _            -> takePrim
        FTakeL _           -> takeLift
        FDrop _            -> dropPrim
        FDropL _           -> dropLift
        FZip _             -> zipPrim
        FZipL _            -> zipLift
        FCartProduct _     -> cartProductPrim
        FCartProductL _    -> cartProductLift
        FNestProduct _     -> nestProductPrim
        FNestProductL _    -> nestProductLift
        FEquiJoin e1 e2 _  -> equiJoinPrim e1 e2
        FEquiJoinL e1 e2 _ -> equiJoinLift e1 e2
        FNestJoin e1 e2 _  -> nestJoinPrim e1 e2
        FNestJoinL e1 e2 _ -> nestJoinLift e1 e2
        FSemiJoin e1 e2 _  -> semiJoinPrim e1 e2
        FSemiJoinL e1 e2 _ -> semiJoinLift e1 e2
        FAntiJoin e1 e2 _  -> antiJoinPrim e1 e2
        FAntiJoinL e1 e2 _ -> antiJoinLift e1 e2
        FTakeWith _        -> takeWithS
        FTakeWithL _       -> takeWithL
        FDropWith _        -> dropWithS
        FDropWithL _       -> dropWithL

constructClosureEnv :: [String] -> Graph a [(String, Shape)]
constructClosureEnv [] = return []
constructClosureEnv (x:xs) = liftM2 (:) (liftM (x,) $ fromGam x) (constructClosureEnv xs)

-- For each top node, determine the number of columns the vector has and insert
-- a dummy projection which just copies those columns. This is to ensure that
-- columns which are required from the top are not pruned by optimizations.
insertTopProjections :: Graph VL Shape -> Graph VL (QP.TopShape DVec)
insertTopProjections g = do
  shape <- g
  let shape' = QP.exportShape shape
  traverseShape shape'
  
  where 
  traverseShape :: (QP.TopShape DVec) -> Graph VL (QP.TopShape DVec)
  traverseShape (QP.ValueVector (DVec q _) lyt) = 
      insertProj lyt q Project DVec QP.ValueVector
  traverseShape (QP.PrimVal (DVec q _) lyt)     = 
      insertProj lyt q Project DVec QP.PrimVal
  
  traverseLayout :: (QP.TopLayout DVec) -> Graph VL (QP.TopLayout DVec)
  traverseLayout (QP.InColumn c) = 
      return $ QP.InColumn c
  traverseLayout (QP.Pair lyt1 lyt2) = do
      lyt1' <- traverseLayout lyt1
      lyt2' <- traverseLayout lyt2
      return $ QP.Pair lyt1' lyt2'
  traverseLayout (QP.Nest (DVec q _) lyt) = 
    insertProj lyt q Project DVec QP.Nest
    
  insertProj 
    :: QP.TopLayout DVec               -- The node's layout
    -> AlgNode                         -- The top node to consider
    -> ([Expr1] -> UnOp)               -- Constructor for the projection op
    -> (AlgNode -> [DBCol] -> v)       -- DVecector constructor
    -> (v -> (QP.TopLayout DVec) -> t) -- Layout/Shape constructor
    -> Graph VL t
  insertProj lyt q project vector describe = do
      let width = QP.columnsInLayout lyt
          cols  = [1 .. width]
      qp   <- insertNode $ UnOp (project $ map Column1 cols) q
      lyt' <- traverseLayout lyt
      return $ describe (vector qp cols) lyt'

-- | Compile a FKL expression into a query plan of vector operators (VL)
specializeVectorOps :: Expr -> QP.QueryPlan VL
specializeVectorOps e = QP.mkQueryPlan opMap shape tagMap
  where
    (opMap, shape, tagMap) = runGraph emptyVL (insertTopProjections $ fkl2VL e)
