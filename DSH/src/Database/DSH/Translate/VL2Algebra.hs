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
         | RDVec    AlgNode [DBCol]
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

fromProp :: PVec -> Res
fromProp (PVec p) = Prop p

toProp :: Res -> PVec
toProp (Prop p) = PVec p
toProp _       = error "toProp: Not a prop vector"

fromRenameVector :: RVec -> Res
fromRenameVector (RVec r) = Rename r

toRenameVector :: Res -> RVec
toRenameVector (Rename r) = RVec r
toRenameVector _       = error "toRenameVector: Not a rename vector"

fromDVec :: DVec -> Res
fromDVec (DVec n cs) = RDVec n cs

toDVec :: Res -> DVec
toDVec (RDVec n cs) = DVec n cs
toDVec _           = error "toDVec: Not a DVec"

vl2Algebra :: VectorAlgebra a => (NodeMap VL, TopShape) -> G a TopShape
vl2Algebra (nodes, plan) = do
                            mapM_ translate roots
                            refreshShape plan
    where
      roots :: [AlgNode]
      roots = rootsFromTopShape plan

      refreshShape :: VectorAlgebra a => TopShape -> G a TopShape
      refreshShape (ValueVector (DVec n _) lyt) = do

                                                 v <- fromDict n
                                                 case v of
                                                     (Just n') -> do
                                                                             lyt' <- refreshLyt lyt
                                                                             return $ ValueVector (toDVec n') lyt'
                                                     _ -> error $ "Disaster: " ++ show v
      refreshShape (PrimVal (DVec n _) lyt) = do
                                             (Just (RDBP n' cs)) <- fromDict n
                                             lyt' <- refreshLyt lyt
                                             return $ PrimVal (DVec n' cs) lyt'

      refreshLyt :: VectorAlgebra a => TopLayout -> G a TopLayout
      refreshLyt l@(InColumn _) = return l
      refreshLyt (Nest (DVec n _) lyt) = do
                                         (Just n') <- fromDict n
                                         lyt' <- refreshLyt lyt
                                         return $ Nest (toDVec n') lyt'
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
                                             (d, r1, r2) <- vecCombine (toDVec c1) (toDVec c2) (toDVec c3)
                                             return $ RTriple (fromDVec d) (fromRenameVector r1) (fromRenameVector r2)

translateBinOp :: VectorAlgebra a => V.BinOp -> Res -> Res -> GraphM () a Res
translateBinOp b c1 c2 = case b of
                           GroupBy          -> do
                                                (d, v, p) <- vecGroupBy (toDVec c1) (toDVec c2)
                                                return $ RTriple (fromDVec d) (fromDVec v) (fromProp p)
                           SortWith         -> do
                                                (d, p) <- vecSort (toDVec c1) (toDVec c2)
                                                return $ RPair (fromDVec d) (fromProp p)
                           LengthSeg        -> liftM fromDVec $ vecLengthS (toDVec c1) (toDVec c2)
                           DistPrim         -> do
                                                (v, p) <- vecDistPrim (toDVec c1) (toDVec c2)
                                                return $ RPair (fromDVec v) (fromProp p)
                           DistDesc         -> do
                                                (v, p) <- vecDistDesc (toDVec c1) (toDVec c2)
                                                return $ RPair (fromDVec v) (fromProp p)
                           DistLift         -> do
                                                (v, p) <- vecDistSeg (toDVec c1) (toDVec c2)
                                                return $ RPair (fromDVec v) (fromProp p)
                           PropRename       -> liftM fromDVec $ vecPropRename (toRenameVector c1) (toDVec c2)
                           PropFilter       -> do
                                                (v, r) <- vecPropFilter (toRenameVector c1) (toDVec c2)
                                                return $ RPair (fromDVec v) (fromRenameVector r)
                           PropReorder      -> do
                                                (v, p) <- vecPropReorder (toProp c1) (toDVec c2)
                                                return $ RPair (fromDVec v) (fromProp p)
                           Append           -> do
                                                (v, r1, r2) <- vecAppend (toDVec c1) (toDVec c2)
                                                return $ RTriple (fromDVec v) (fromRenameVector r1) (fromRenameVector r2)
                           RestrictVec      -> do
                                                (v, r) <- vecRestrict (toDVec c1) (toDVec c2)
                                                return $ RPair (fromDVec v) (fromRenameVector r)
                           CompExpr2 e      -> undefined
                           CompExpr2L e     -> liftM fromDVec $ vecBinExpr e (toDVec c1) (toDVec c2)
                           VecSumL          -> liftM fromDVec $ vecSumS (toDVec c1) (toDVec c2)
                           VecAvgL          -> liftM fromDVec $ vecAvgS (toDVec c1) (toDVec c2)
                           SelectPos o      -> do
                                                (v, r) <- selectPos (toDVec c1) o (toDVec c2)
                                                return $ RPair (fromDVec v) (fromRenameVector r)
                           SelectPosL o     -> do
                                                (v, r) <- selectPosS (toDVec c1) o (toDVec c2)
                                                return $ RPair (fromDVec v) (fromRenameVector r)
                           PairA            -> undefined
                           PairL            -> liftM fromDVec $ vecZip (toDVec c1) (toDVec c2)
                           ZipL             -> do
                                                (v, r1 ,r2) <- vecZipS (toDVec c1) (toDVec c2)
                                                return $ RTriple (fromDVec v) (fromRenameVector r1) (fromRenameVector r2)
                           CartProduct      -> do
                                                (v, p1, p2) <- vecCartProduct (toDVec c1) (toDVec c2)
                                                return $ RTriple (fromDVec v) (fromProp p1) (fromProp p2)
                           CartProductL     -> do
                                                (v, p1, p2) <- vecCartProductS (toDVec c1) (toDVec c2)
                                                return $ RTriple (fromDVec v) (fromProp p1) (fromProp p2)
                           (EquiJoin e1 e2) -> do
                                                (v, p1, p2) <- vecEquiJoin e1 e2 (toDVec c1) (toDVec c2)
                                                return $ RTriple (fromDVec v) (fromProp p1) (fromProp p2)
                           (EquiJoinL e1 e2) -> do
                                                (v, p1, p2) <- vecEquiJoinS e1 e2 (toDVec c1) (toDVec c2)
                                                return $ RTriple (fromDVec v) (fromProp p1) (fromProp p2)
                           (SemiJoin e1 e2) -> do
                                                (v, r) <- vecSemiJoin e1 e2 (toDVec c1) (toDVec c2)
                                                return $ RPair (fromDVec v) (fromRenameVector r)
                           (SemiJoinL e1 e2) -> do
                                                (v, r) <- vecSemiJoinS e1 e2 (toDVec c1) (toDVec c2)
                                                return $ RPair (fromDVec v) (fromRenameVector r)
                           (AntiJoin e1 e2) -> do
                                                (v, r) <- vecAntiJoin e1 e2 (toDVec c1) (toDVec c2)
                                                return $ RPair (fromDVec v) (fromRenameVector r)
                           (AntiJoinL e1 e2) -> do
                                                (v, r) <- vecAntiJoinS e1 e2 (toDVec c1) (toDVec c2)
                                                return $ RPair (fromDVec v) (fromRenameVector r)

singleton :: Res -> Res
singleton (RDBP c cs) = RDVec c cs
singleton _           = error "singleton: Not a DBP"

only :: Res -> Res
only (RDVec c cs) = RDBP c cs
only _           = error "only: Not a DVec"

translateUnOp :: VectorAlgebra a => UnOp -> Res -> GraphM () a Res
translateUnOp u c = case u of
                      Singleton     -> return $ singleton c
                      Only          -> return $ only c
                      Unique        -> liftM fromDVec $ vecUnique (toDVec c)
                      UniqueL       -> liftM fromDVec $ vecUniqueS (toDVec c)
                      Number        -> liftM fromDVec $ vecNumber (toDVec c)
                      NumberL       -> liftM fromDVec $ vecNumberS (toDVec c)
                      LengthA       -> liftM fromDVec $ vecLength (toDVec c)
                      DescToRename  -> liftM fromRenameVector $ descToRename (toDVec c)
                      Segment       -> liftM fromDVec $ vecSegment (toDVec c)
                      Unsegment     -> liftM fromDVec $ vecUnsegment (toDVec c)
                      VecSum ty     -> liftM fromDVec $ vecSum ty (toDVec c)
                      VecAvg        -> liftM fromDVec $ vecAvg (toDVec c)
                      VecMin        -> liftM fromDVec $ vecMin (toDVec c)
                      VecMinL       -> liftM fromDVec $ vecMinS (toDVec c)
                      VecMax        -> liftM fromDVec $ vecMax (toDVec c)
                      VecMaxL       -> liftM fromDVec $ vecMaxS (toDVec c)
                      SelectExpr e  -> liftM fromDVec $ vecSelect e (toDVec c)
                      ProjectRename (posnewP, posoldP) -> liftM fromRenameVector $ projectRename posnewP posoldP (toDVec c)
                      VLProject cols -> liftM fromDVec $ vecProject cols (toDVec c)
                      VLProjectA cols -> undefined
                      ReverseA      -> do
                                        (d, p) <- vecReverse (toDVec c)
                                        return $ RPair (fromDVec d) (fromProp p)
                      ReverseL      -> do
                                        (d, p) <- vecReverseS (toDVec c)
                                        return $ RPair (fromDVec d) (fromProp p)
                      FalsePositions -> liftM fromDVec $ falsePositions (toDVec c)
                      SelectPos1 op pos -> do
                                         (d, p) <- selectPos1 (toDVec c) op pos
                                         return $ RPair (fromDVec d) (fromRenameVector p)
                      SelectPos1L op pos -> do
                                          (d, p) <- selectPos1S (toDVec c) op pos
                                          return $ RPair (fromDVec d) (fromRenameVector p)
                      VecAggr g as -> liftM fromDVec $ vecAggr g as (toDVec c)
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
translateNullary SingletonDescr                   = liftM fromDVec $ singletonDescr
translateNullary (ConstructLiteralValue tys vals) = undefined
translateNullary (ConstructLiteralTable tys vals) = liftM fromDVec $ vecLit tys vals
translateNullary (TableRef n tys ks)              = liftM fromDVec $ vecTableRef n tys ks

implementVectorOpsX100 :: QueryPlan VL -> QueryPlan X100Algebra
implementVectorOpsX100 vlPlan =
  let (opMap, shape, tagMap)= runG dummy (vl2Algebra (nodeMap $ queryDag vlPlan, queryShape vlPlan))
  in mkQueryPlan opMap shape tagMap

implementVectorOpsPF :: QueryPlan VL -> QueryPlan PFAlgebra
implementVectorOpsPF vlPlan =
  let (opMap, shape, tagMap)= runG initLoop (vl2Algebra (nodeMap $ queryDag vlPlan, queryShape vlPlan))
  in mkQueryPlan opMap shape tagMap
