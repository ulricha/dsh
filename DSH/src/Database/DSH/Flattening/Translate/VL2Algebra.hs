module Database.DSH.Flattening.Translate.VL2Algebra
       ( toPFAlgebra
       , toXML
       , toX100Algebra
       , toX100String
       , toX100File
       , vlDagtoX100Dag
       , importShape
       , exportShape
       , toVLFile) where

import           Data.List                                             (intercalate)

import           Database.Algebra.Pathfinder                           (PFAlgebra)

import           Database.Algebra.Pathfinder                           (initLoop)
import           Database.Algebra.Pathfinder.Render.XML                hiding (Graph, XML, getNode, node)
import           Database.Algebra.X100.Data                            (X100Algebra)
import           Database.Algebra.X100.Data.Create                     (dummy)
import           Database.Algebra.X100.JSON
import           Database.Algebra.X100.Render
import           Database.DSH.Flattening.VL.PathfinderVectorPrimitives ()

import qualified Data.IntMap                                           as IM
import qualified Data.Map                                              as M

import           Database.Algebra.Aux
import           Database.Algebra.Dag                                  (AlgebraDag, mkDag, nodeMap)
import           Database.Algebra.Dag.Builder
import           Database.Algebra.Dag.Common                           hiding (BinOp)
import qualified Database.Algebra.Dag.Common                           as C
import           Database.Algebra.VL.Data                              hiding (DBCol)
import qualified Database.Algebra.VL.Data                              as V
import qualified Database.Algebra.VL.Render.JSON                       as VLJSON
import           Database.DSH.Flattening.Translate.FKL2VL              ()
import           Database.DSH.Flattening.VL.Data.DBVector
import           Database.DSH.Flattening.VL.Data.GraphVector           hiding (Pair)
import qualified Database.DSH.Flattening.VL.Data.GraphVector           as Vec
import qualified Database.DSH.Flattening.VL.Data.GraphVector           as GV
import qualified Database.DSH.Flattening.VL.Data.Query                 as Ext
import           Database.DSH.Flattening.VL.VectorPrimitives
import           Database.DSH.Flattening.VL.X100VectorPrimitives       ()

import qualified Database.DSH.Flattening.VL.Data.TopShape              as TS

import           Control.Monad.State

type G alg = StateT (M.Map AlgNode Res) (GraphM () alg)

runG :: VectorAlgebra a => a -> G a r -> AlgPlan a r
runG i c = runGraph i $ liftM fst $ runStateT c M.empty

data Res = Prop    AlgNode
         | Rename  AlgNode
         | RDBV    AlgNode [DBCol]
         | RDBP    AlgNode [DBCol]
         | Descr   AlgNode
         | RPair    Res Res
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
toDBV (Descr n)   = DBV n []
toDBV _           = error "toDBV: Not a DBV"

fromDBP :: DBP -> Res
fromDBP (DBP n cs) = RDBP n cs

toDBP :: Res -> DBP
toDBP (RDBP n cs) = DBP n cs
toDBP _           = error "toDBP: Not a DBP"

fromDescrVector :: DescrVector -> Res
fromDescrVector (DescrVector d) = Descr d

toDescrVector :: Res -> DescrVector
toDescrVector (Descr d) = DescrVector d
toDescrVector _         = error "toDescrVector: Not a descriptor vector"

vl2Algebra :: VectorAlgebra a => (NodeMap VL, Shape) -> G a Shape
vl2Algebra (nodes, plan) = do
                            mapM_ translate roots
                            refreshShape plan
    where
      roots :: [AlgNode]
      roots = rootNodes plan
      refreshShape :: VectorAlgebra a => Shape -> G a Shape
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
      refreshShape _ = error "refreshShape: Closure cannot be translated to algebra"
      refreshLyt :: VectorAlgebra a => Layout -> G a Layout
      refreshLyt l@(InColumn _) = return l
      refreshLyt (Nest (DBV n _) lyt) = do
                                         (Just n') <- fromDict n
                                         lyt' <- refreshLyt lyt
                                         return $ Nest (toDBV n') lyt'
      refreshLyt (GV.Pair l1 l2) = do
                                 l1' <- refreshLyt l1
                                 l2' <- refreshLyt l2
                                 return $ GV.Pair l1' l2'
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
                                                (d, v, p) <- groupBy (toDBV c1) (toDBV c2)
                                                return $ RTriple (fromDescrVector d) (fromDBV v) (fromProp p)
                           SortWith         -> do
                                                (d, p) <- sortWith (toDBV c1) (toDBV c2)
                                                return $ RPair (fromDBV d) (fromProp p)
                           LengthSeg        -> liftM fromDBV $ lengthSeg (toDescrVector c1) (toDescrVector c2)
                           DistPrim         -> do
                                                (v, p) <- distPrim (toDBP c1) (toDescrVector c2)
                                                return $ RPair (fromDBV v) (fromProp p)
                           DistDesc         -> do
                                                (v, p) <- distDesc (toDBV c1) (toDescrVector c2)
                                                return $ RPair (fromDBV v) (fromProp p)
                           DistLift         -> do
                                                (v, p) <- distLift (toDBV c1) (toDescrVector c2)
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
                           VecSumL          -> liftM fromDBV $ vecSumLift (toDescrVector c1) (toDBV c2)
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
                           ThetaJoin     js -> do
                                                (v1, v2) <- thetaJoin js (toDBV c1) (toDBV c2)
                                                return $ RPair (fromDBV v1) (fromDBV v2)


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
                      NotPrim       -> liftM fromDBP $ notPrim (toDBP c)
                      NotVec        -> liftM fromDBV $ notVec (toDBV c)
                      LengthA       -> liftM fromDBP $ lengthA (toDescrVector c)
                      DescToRename  -> liftM fromRenameVector $ descToRename (toDescrVector c)
                      ToDescr       -> liftM fromDescrVector $ toDescr (toDBV c)
                      Segment       -> liftM fromDBV $ segment (toDBV c)
                      Unsegment     -> liftM fromDBV $ unsegment (toDBV c)
                      VecSum ty     -> liftM fromDBP $ vecSum ty (toDBV c)
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
translateNullary SingletonDescr                   = liftM fromDescrVector $ singletonDescr
translateNullary (ConstructLiteralValue tys vals) = liftM fromDBP $ constructLiteralValue tys vals
translateNullary (ConstructLiteralTable tys vals) = liftM fromDBV $ constructLiteralTable tys vals
translateNullary (TableRef n tys ks)              = liftM fromDBV $ tableRef n tys ks


toPFAlgebra :: AlgPlan VL Shape -> AlgPlan PFAlgebra Shape
toPFAlgebra (n, r, _) = runG initLoop (vl2Algebra (reverseAlgMap n, r))

toX100Algebra :: AlgPlan VL Shape -> AlgPlan X100Algebra Shape
toX100Algebra (n, r, _) = runG dummy (vl2Algebra (reverseAlgMap n, r))

vlDagtoX100Dag :: AlgebraDag VL -> TS.TopShape -> (AlgebraDag X100Algebra, TS.TopShape)
vlDagtoX100Dag vlDag shape =
  -- FIXME the conversion of IntMap to Map sucks big time.
  let vlplan = ((reverseMap $ M.fromList . IM.toList $ nodeMap vlDag), importShape shape, IM.empty)
      (m, shape', _) = toX100Algebra vlplan
  in (mkDag (reverseToIntMap m) (rootNodes shape'), exportShape shape')

toX100File :: FilePath -> AlgPlan X100Algebra Shape -> IO ()
toX100File f (m, r, t) = do
    planToFile f (t, rootNodes r, reverseAlgMap m)

toVLFile :: FilePath -> AlgPlan VL Shape -> IO ()
toVLFile prefix (m, r, t) = do
    let planPath = prefix ++ "_vl.plan"
        shapePath = prefix ++ "_shape.plan"
    VLJSON.planToFile planPath (t, rootNodes r, reverseAlgMap m)
    writeFile shapePath $ show $ exportShape r

importShape :: TS.TopShape -> Shape
importShape (TS.ValueVector (DBV n cols) lyt) = Vec.ValueVector (DBV n cols) (importLayout lyt)
importShape (TS.PrimVal (DBP n cols) lyt)     = Vec.PrimVal (DBP n cols) (importLayout lyt)

importLayout :: TS.TopLayout -> Layout
importLayout (TS.InColumn i)              = Vec.InColumn i
importLayout (TS.Nest (DBV n cols) lyt) = Vec.Nest (DBV n cols) (importLayout lyt)
importLayout (TS.Pair lyt1 lyt2)          = Vec.Pair (importLayout lyt1) (importLayout lyt2)

exportShape :: Shape -> TS.TopShape
exportShape (Vec.ValueVector (DBV n cols) lyt) = TS.ValueVector (DBV n cols) (exportLayout lyt)
exportShape (Vec.PrimVal (DBP n cols) lyt)     = TS.PrimVal (DBP n cols) (exportLayout lyt)
exportShape s                                  = error $ "exportShape: impossible top-level shape " ++ (show s)

exportLayout :: Layout -> TS.TopLayout
exportLayout (Vec.InColumn i)            = TS.InColumn i
exportLayout (Vec.Nest (DBV n cols) lyt) = TS.Nest (DBV n cols) (exportLayout lyt)
exportLayout (Vec.Pair lyt1 lyt2)        = TS.Pair (exportLayout lyt1) (exportLayout lyt2)

toX100String :: AlgPlan X100Algebra Shape -> Ext.Query Ext.X100
toX100String (m, r, _t) = convertQuery r
 where
    m' :: NodeMap X100Algebra
    m' = reverseAlgMap m
    convertQuery :: Shape -> Ext.Query Ext.X100
    convertQuery (PrimVal (DBP r' _) l) = Ext.PrimVal (Ext.X100 r' $ generateDumbQuery m' r') $ convertLayout l
    convertQuery (ValueVector (DBV r' _) l) = Ext.ValueVector (Ext.X100 r' $ generateDumbQuery m' r') $ convertLayout l
    convertQuery (Closure _ _ _ _ _) = error "Functions cannot appear as a result value"
    convertQuery (AClosure _ _ _ _ _ _ _) = error "Function cannot appear as a result value"
    convertLayout :: Layout -> Ext.Layout Ext.X100
    convertLayout (InColumn i) = Ext.InColumn i
    convertLayout (Nest (DBV r' _) l) = Ext.Nest (Ext.X100 r' $ generateDumbQuery m' r') $ convertLayout l
    convertLayout (Vec.Pair p1 p2) = Ext.Pair (convertLayout p1) (convertLayout p2)

toXML :: AlgPlan PFAlgebra Shape -> Ext.Query Ext.XML
toXML (g, r, ts) = convertQuery r
    where
        convertQuery :: Shape -> Ext.Query Ext.XML
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
                        runXML False M.empty IM.empty $
                            mkQueryPlan Nothing (xmlElem "property") $
                                runXML True nodeTable ts $ serializeAlgebra cs n
