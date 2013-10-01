module Database.DSH.Translate.VL2Algebra(implementVectorOpsX100 , implementVectorOpsPF) where

import           Data.List                                             (intercalate)

import           Database.Algebra.Pathfinder                           (PFAlgebra)

import           Database.Algebra.Pathfinder                           (initLoop)
import           Database.Algebra.X100.Data                            (X100Algebra)
import           Database.Algebra.X100.Data.Create                     (dummy)
import           Database.DSH.VL.PathfinderVectorPrimitives ()

import qualified Data.IntMap                                           as IM
import qualified Data.Map                                              as M

import           Database.Algebra.Dag                                  (AlgebraDag, nodeMap)
import           Database.Algebra.Dag.Builder
import           Database.Algebra.Dag.Common                           hiding (BinOp)
import qualified Database.Algebra.Dag.Common                           as C
import           Database.Algebra.VL.Data                              hiding (DBCol, Pair)
import qualified Database.Algebra.VL.Data                              as V
import           Database.DSH.Translate.FKL2VL              ()
import           Database.DSH.VL.Data.DBVector
import           Database.DSH.VL.VectorPrimitives
import           Database.DSH.VL.X100VectorPrimitives       ()

import           Database.DSH.Common.Data.QueryPlan

import           Control.Monad.State

type G alg = StateT (M.Map AlgNode Res) (GraphM () alg)

runG :: VectorAlgebra a => a -> G a r -> AlgPlan a r
runG i c = runGraph i $ liftM fst $ runStateT c M.empty

data Res = Prop    AlgNode
         | Rename  AlgNode
         | RDBV    AlgNode [DBCol]
         | RDBP    AlgNode [DBCol]
         | RPair   Res Res
         | RTriple Res Res Res
    deriving Show

fromDict :: VectorAlgebra a => AlgNode -> G a (Maybe Res)
fromDict n = do
                dict <- get
                return $ M.lookup n dict

insertTranslation :: VectorAlgebra a => AlgNode -> Res -> G a ()
insertTranslation n res = modify (M.insert n res)

fromProp :: PropVector -> Res
fromProp (PropVector p) = Prop p

toProp :: Res -> PropVector
toProp (Prop p) = PropVector p
toProp _       = error "toProp: Not a prop vector"

fromRenameVector :: RenameVector -> Res
fromRenameVector (RenameVector r) = Rename r

toRenameVector :: Res -> RenameVector
toRenameVector (Rename r) = RenameVector r
toRenameVector _       = error "toRenameVector: Not a rename vector"

fromDBV :: DBV -> Res
fromDBV (DBV n cs) = RDBV n cs

toDBV :: Res -> DBV
toDBV (RDBV n cs) = DBV n cs
toDBV _           = error "toDBV: Not a DBV"

fromDBP :: DBP -> Res
fromDBP (DBP n cs) = RDBP n cs

toDBP :: Res -> DBP
toDBP (RDBP n cs) = DBP n cs
toDBP _           = error "toDBP: Not a DBP"

vl2Algebra :: VectorAlgebra a => (NodeMap VL, TopShape) -> G a TopShape
vl2Algebra (nodes, plan) = do
                            mapM_ translate roots
                            refreshShape plan
    where
      roots :: [AlgNode]
      roots = rootsFromTopShape plan

      refreshShape :: VectorAlgebra a => TopShape -> G a TopShape
      refreshShape (ValueVector (DBV n _) lyt) = do

                                                 v <- fromDict n
                                                 case v of
                                                     (Just n') -> do
                                                                             lyt' <- refreshLyt lyt
                                                                             return $ ValueVector (toDBV n') lyt'
                                                     _ -> error $ "Disaster: " ++ show v
      refreshShape (PrimVal (DBP n _) lyt) = do
                                             (Just (RDBP n' cs)) <- fromDict n
                                             lyt' <- refreshLyt lyt
                                             return $ PrimVal (DBP n' cs) lyt'

      refreshLyt :: VectorAlgebra a => TopLayout -> G a TopLayout
      refreshLyt l@(InColumn _) = return l
      refreshLyt (Nest (DBV n _) lyt) = do
                                         (Just n') <- fromDict n
                                         lyt' <- refreshLyt lyt
                                         return $ Nest (toDBV n') lyt'
      refreshLyt (Pair l1 l2) = do
                                 l1' <- refreshLyt l1
                                 l2' <- refreshLyt l2
                                 return $ Pair l1' l2'
      getNode :: AlgNode -> VL
      getNode n = case IM.lookup n nodes of
        Just op -> op
        Nothing -> error $ "getNode: node " ++ (show n) ++ " not in nodes map " ++ (pp nodes)

      pp m = intercalate ",\n" $ map show $ IM.toList m

      translate :: VectorAlgebra a => AlgNode -> G a Res
      translate n = do
                      r <- fromDict n
                      case r of
                        Just res -> return $ res
                        Nothing -> do
                                    let node = getNode n
                                    r' <- case node of
                                        TerOp t c1 c2 c3 -> do
                                            c1' <- translate c1
                                            c2' <- translate c2
                                            c3' <- translate c3
                                            lift $ translateTerOp t c1' c2' c3'
                                        C.BinOp b c1 c2    -> do
                                            c1' <- translate c1
                                            c2' <- translate c2
                                            lift $ translateBinOp b c1' c2'
                                        UnOp u c1        -> do
                                            c1' <- translate c1
                                            lift $ translateUnOp u c1'
                                        NullaryOp o      -> lift $ translateNullary o
                                    insertTranslation n r'
                                    return r'

translateTerOp :: VectorAlgebra a => TerOp -> Res -> Res -> Res -> GraphM () a Res
translateTerOp t c1 c2 c3 = case t of
                             CombineVec -> do
                                             (d, r1, r2) <- combineVec (toDBV c1) (toDBV c2) (toDBV c3)
                                             return $ RTriple (fromDBV d) (fromRenameVector r1) (fromRenameVector r2)

translateBinOp :: VectorAlgebra a => V.BinOp -> Res -> Res -> GraphM () a Res
translateBinOp b c1 c2 = case b of
                           GroupBy          -> do
                                                (d, v, p) <- groupByKey (toDBV c1) (toDBV c2)
                                                return $ RTriple (fromDBV d) (fromDBV v) (fromProp p)
                           SortWith         -> do
                                                (d, p) <- sortWith (toDBV c1) (toDBV c2)
                                                return $ RPair (fromDBV d) (fromProp p)
                           LengthSeg        -> liftM fromDBV $ lengthSeg (toDBV c1) (toDBV c2)
                           DistPrim         -> do
                                                (v, p) <- distPrim (toDBP c1) (toDBV c2)
                                                return $ RPair (fromDBV v) (fromProp p)
                           DistDesc         -> do
                                                (v, p) <- distDesc (toDBV c1) (toDBV c2)
                                                return $ RPair (fromDBV v) (fromProp p)
                           DistLift         -> do
                                                (v, p) <- distLift (toDBV c1) (toDBV c2)
                                                return $ RPair (fromDBV v) (fromProp p)
                           PropRename       -> liftM fromDBV $ propRename (toRenameVector c1) (toDBV c2)
                           PropFilter       -> do
                                                (v, r) <- propFilter (toRenameVector c1) (toDBV c2)
                                                return $ RPair (fromDBV v) (fromRenameVector r)
                           PropReorder      -> do
                                                (v, p) <- propReorder (toProp c1) (toDBV c2)
                                                return $ RPair (fromDBV v) (fromProp p)
                           Append           -> do
                                                (v, r1, r2) <- append (toDBV c1) (toDBV c2)
                                                return $ RTriple (fromDBV v) (fromRenameVector r1) (fromRenameVector r2)
                           RestrictVec      -> do
                                                (v, r) <- restrictVec (toDBV c1) (toDBV c2)
                                                return $ RPair (fromDBV v) (fromRenameVector r)
                           CompExpr2 e      -> liftM fromDBP $ compExpr2 e (toDBP c1) (toDBP c2)
                           CompExpr2L e     -> liftM fromDBV $ compExpr2L e (toDBV c1) (toDBV c2)
                           VecSumL          -> liftM fromDBV $ vecSumLift (toDBV c1) (toDBV c2)
                           VecAvgL          -> liftM fromDBV $ vecAvgLift (toDBV c1) (toDBV c2)
                           SelectPos o      -> do
                                                (v, r) <- selectPos (toDBV c1) o (toDBP c2)
                                                return $ RPair (fromDBV v) (fromRenameVector r)
                           SelectPosL o     -> do
                                                (v, r) <- selectPosLift (toDBV c1) o (toDBV c2)
                                                return $ RPair (fromDBV v) (fromRenameVector r)
                           PairA            -> liftM fromDBP $ pairA (toDBP c1) (toDBP c2)
                           PairL            -> liftM fromDBV $ pairL (toDBV c1) (toDBV c2)
                           ZipL             -> do
                                                (v, r1 ,r2) <- zipL (toDBV c1) (toDBV c2)
                                                return $ RTriple (fromDBV v) (fromRenameVector r1) (fromRenameVector r2)
                           CartProduct      -> do
                                                (v, p1, p2) <- cartProduct (toDBV c1) (toDBV c2)
                                                return $ RTriple (fromDBV v) (fromProp p1) (fromProp p2)
                           CartProductL     -> do
                                                (v, p1, p2) <- cartProductL (toDBV c1) (toDBV c2)
                                                return $ RTriple (fromDBV v) (fromProp p1) (fromProp p2)
                           (EquiJoin e1 e2) -> do
                                                (v, p1, p2) <- equiJoin e1 e2 (toDBV c1) (toDBV c2)
                                                return $ RTriple (fromDBV v) (fromProp p1) (fromProp p2)
                           (EquiJoinL e1 e2) -> do
                                                (v, p1, p2) <- equiJoinL e1 e2 (toDBV c1) (toDBV c2)
                                                return $ RTriple (fromDBV v) (fromProp p1) (fromProp p2)
                           (SemiJoin e1 e2) -> do
                                                (v, r) <- semiJoin e1 e2 (toDBV c1) (toDBV c2)
                                                return $ RPair (fromDBV v) (fromRenameVector r)
                           (SemiJoinL e1 e2) -> do
                                                (v, r) <- semiJoinL e1 e2 (toDBV c1) (toDBV c2)
                                                return $ RPair (fromDBV v) (fromRenameVector r)
                           (AntiJoin e1 e2) -> do
                                                (v, r) <- antiJoin e1 e2 (toDBV c1) (toDBV c2)
                                                return $ RPair (fromDBV v) (fromRenameVector r)
                           (AntiJoinL e1 e2) -> do
                                                (v, r) <- antiJoinL e1 e2 (toDBV c1) (toDBV c2)
                                                return $ RPair (fromDBV v) (fromRenameVector r)

singleton :: Res -> Res
singleton (RDBP c cs) = RDBV c cs
singleton _           = error "singleton: Not a DBP"

only :: Res -> Res
only (RDBV c cs) = RDBP c cs
only _           = error "only: Not a DBV"

translateUnOp :: VectorAlgebra a => UnOp -> Res -> GraphM () a Res
translateUnOp u c = case u of
                      Singleton     -> return $ singleton c
                      Only          -> return $ only c
                      Unique        -> liftM fromDBV $ unique (toDBV c)
                      UniqueL       -> liftM fromDBV $ uniqueL (toDBV c)
                      Number        -> liftM fromDBV $ unique (toDBV c)
                      NumberL       -> liftM fromDBV $ uniqueL (toDBV c)
                      NotPrim       -> liftM fromDBP $ notPrim (toDBP c)
                      NotVec        -> liftM fromDBV $ notVec (toDBV c)
                      LengthA       -> liftM fromDBP $ lengthA (toDBV c)
                      DescToRename  -> liftM fromRenameVector $ descToRename (toDBV c)
                      Segment       -> liftM fromDBV $ segment (toDBV c)
                      Unsegment     -> liftM fromDBV $ unsegment (toDBV c)
                      VecSum ty     -> liftM fromDBP $ vecSum ty (toDBV c)
                      VecAvg        -> liftM fromDBP $ vecAvg (toDBV c)
                      VecMin        -> liftM fromDBP $ vecMin (toDBV c)
                      VecMinL       -> liftM fromDBV $ vecMinLift (toDBV c)
                      VecMax        -> liftM fromDBP $ vecMax (toDBV c)
                      VecMaxL       -> liftM fromDBV $ vecMaxLift (toDBV c)
                      SelectExpr e  -> liftM fromDBV $ selectExpr e (toDBV c)
                      ProjectRename (posnewP, posoldP) -> liftM fromRenameVector $ projectRename posnewP posoldP (toDBV c)
                      ProjectPayload valPs -> liftM fromDBV $ projectPayload valPs (toDBV c)
                      ProjectAdmin (descrP, posP) -> liftM fromDBV $ projectAdmin descrP posP (toDBV c)
                      ProjectL cols -> liftM fromDBV $ projectL (toDBV c) cols
                      ProjectA cols -> liftM fromDBP $ projectA (toDBP c) cols
                      IntegerToDoubleA -> liftM fromDBP $ integerToDoubleA (toDBP c)
                      IntegerToDoubleL -> liftM fromDBV $ integerToDoubleL (toDBV c)
                      CompExpr1L e   -> liftM fromDBV $ compExpr1 e (toDBV c)
                      ReverseA      -> do
                                        (d, p) <- reverseA (toDBV c)
                                        return $ RPair (fromDBV d) (fromProp p)
                      ReverseL      -> do
                                        (d, p) <- reverseL (toDBV c)
                                        return $ RPair (fromDBV d) (fromProp p)
                      FalsePositions -> liftM fromDBV $ falsePositions (toDBV c)
                      SelectPos1 op pos -> do
                                         (d, p) <- selectPos1 (toDBV c) op pos
                                         return $ RPair (fromDBV d) (fromRenameVector p)
                      SelectPos1L op pos -> do
                                          (d, p) <- selectPos1Lift (toDBV c) op pos
                                          return $ RPair (fromDBV d) (fromRenameVector p)
                      VecAggr g as -> liftM fromDBV $ vecAggr g as (toDBV c)
                      R1            -> case c of
                                         (RPair c1 _)     -> return c1
                                         (RTriple c1 _ _) -> return c1
                                         _                -> error "R1: Not a tuple"
                      R2            -> case c of
                                        (RPair _ c2)     -> return c2
                                        (RTriple _ c2 _) -> return c2
                                        _                -> error "R2: Not a tuple"
                      R3            -> case c of
                                        (RTriple _ _ c3) -> return c3
                                        _                -> error "R3: Not a tuple"


translateNullary :: VectorAlgebra a => NullOp -> GraphM () a Res
translateNullary SingletonDescr                   = liftM fromDBV $ singletonDescr
translateNullary (ConstructLiteralValue tys vals) = liftM fromDBP $ constructLiteralValue tys vals
translateNullary (ConstructLiteralTable tys vals) = liftM fromDBV $ constructLiteralTable tys vals
translateNullary (TableRef n tys ks)              = liftM fromDBV $ tableRef n tys ks

implementVectorOpsX100 :: QueryPlan VL -> QueryPlan X100Algebra
implementVectorOpsX100 vlPlan =
  let (opMap, shape, tagMap)= runG dummy (vl2Algebra (nodeMap $ queryDag vlPlan, queryShape vlPlan))
  in mkQueryPlan opMap shape tagMap

implementVectorOpsPF :: QueryPlan VL -> QueryPlan PFAlgebra
implementVectorOpsPF vlPlan =
  let (opMap, shape, tagMap)= runG initLoop (vl2Algebra (nodeMap $ queryDag vlPlan, queryShape vlPlan))
  in mkQueryPlan opMap shape tagMap


