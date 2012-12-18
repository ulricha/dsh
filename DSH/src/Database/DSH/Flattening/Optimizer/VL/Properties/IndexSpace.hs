module Database.DSH.Flattening.Optimizer.VL.Properties.IndexSpace where

import           Database.Algebra.Dag.Common
import           Database.Algebra.VL.Data

import           Database.DSH.Flattening.Optimizer.VL.Properties.AbstractDomains
import           Database.DSH.Flattening.Optimizer.VL.Properties.Common
import           Database.DSH.Flattening.Optimizer.VL.Properties.Types

unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.IndexSpace"

fromDBV :: IndexSpace -> Either String (DescrIndexSpace, PosIndexSpace)
fromDBV (DBVSpace dis pis)         = Right (dis, pis)
fromDBV (DescrVectorSpace dis pis) = Right (dis, pis)
fromDBV _                          = Left "IndexSpace.fromDBV: not a Value vector/descriptor vector"

fromRenameVector :: IndexSpace -> Either String (SourceIndexSpace, TargetIndexSpace)
fromRenameVector (RenameVectorTransform sis tis) = Right (sis, tis)
fromRenameVector x                               = Left $ "IndexSpace.fromRenameVector: not a rename vector" ++ (show x)

-- Non-Either IndexSpace accessors
descrSpaceDBV :: VectorProp IndexSpace -> Domain
descrSpaceDBV (VProp (DBVSpace (D d) _)) = d
descrSpaceDBV _                          = error "IndexSpace.descrSpaceDBV: not a DBVSpace"

posSpaceDBV :: VectorProp IndexSpace -> Domain
posSpaceDBV (VProp (DBVSpace _ (P p))) = p
posSpaceDBV _                          = error "IndexSpace.posSpaceDBV: not a DBVSpace"

freshSpace :: Show a => AlgNode -> a -> Domain
freshSpace n c = makeSubDomain n c UniverseDom

freshSpaces :: AlgNode -> (DescrIndexSpace, PosIndexSpace)
freshSpaces n =
  (D $ freshSpace n "d", P $ freshSpace n "p")

freshDBVSpace :: AlgNode -> IndexSpace
freshDBVSpace n = uncurry DBVSpace $ freshSpaces n

freshTransformSpaces :: AlgNode -> (SourceIndexSpace, TargetIndexSpace)
freshTransformSpaces n =
  (S $ makeSubDomain n "s" UniverseDom, T $ makeSubDomain n "t" UniverseDom)

freshPropSpace :: AlgNode -> IndexSpace
freshPropSpace n = uncurry PropVectorTransform $ freshTransformSpaces n

freshValuePropPair :: AlgNode -> (IndexSpace, IndexSpace)
freshValuePropPair n =
  (freshDBVSpace n, uncurry PropVectorTransform $ freshTransformSpaces n)

freshValueRenamePair :: AlgNode -> (IndexSpace, IndexSpace)
freshValueRenamePair n =
  (freshDBVSpace n, uncurry RenameVectorTransform $ freshTransformSpaces n)

inferIndexSpaceNullOp :: AlgNode -> NullOp -> Either String (VectorProp IndexSpace)
inferIndexSpaceNullOp n op =
  case op of
    SingletonDescr              -> Right $ VProp $ uncurry DescrVectorSpace $ freshSpaces n
    ConstructLiteralTable _ _   -> Right $ VProp $ freshDBVSpace n
    ConstructLiteralValue _ _   -> Right $ VProp $ DBPSpace $ snd $ freshSpaces n
    TableRef              _ _ _ -> Right $ VProp $ freshDBVSpace n

inferIndexSpaceUnOp :: VectorProp IndexSpace
                       -> AlgNode
                       -> UnOp
                       -> Either String (VectorProp IndexSpace)
inferIndexSpaceUnOp is n op =
  case op of
    Unique -> Right $ VProp $ freshDBVSpace n
    UniqueL -> Right $ VProp $ freshDBVSpace n
    NotPrim -> Right is
    NotVec -> Right is
    LengthA -> Right $ VProp $ DBPSpace $ P $ freshSpace n "p"
    DescToRename -> do
      ((D dis), (P pis)) <- unp is >>= fromDBV
      return $ VProp $ RenameVectorTransform (S pis) (T dis)

    ToDescr -> do
      (dis, pis) <- unp is >>= fromDBV
      return $ VProp $ DescrVectorSpace dis pis

    Segment -> do
      (_, (P pis)) <- unp is >>= fromDBV
      return $ VProp $ DBVSpace (D pis) (P pis)

    Unsegment -> do
      (_, pis) <- unp is >>= fromDBV
      return $ VProp $ DBVSpace (D $ freshSpace n "d") pis

    VecSum _ -> Right $ VProp $ freshDBVSpace n
    VecMin -> Right $ VProp $ freshDBVSpace n
    VecMinL -> Right $ VProp $ freshDBVSpace n
    VecMax -> Right $ VProp $ freshDBVSpace n
    VecMaxL -> Right $ VProp $ freshDBVSpace n

    ProjectL _ -> Right is
    ProjectA _ -> Right is

    IntegerToDoubleA -> Right is
    IntegerToDoubleL -> Right is

    ReverseA -> do
      return $ VPropPair (freshDBVSpace n) (uncurry PropVectorTransform $ freshTransformSpaces n)

    ReverseL -> Right $ VPropPair (freshDBVSpace n) (uncurry PropVectorTransform $ freshTransformSpaces n)
    FalsePositions -> Right $ VProp $ freshDBVSpace n
    SelectPos1 _ _ -> Right $ VPropPair (freshDBVSpace n) (uncurry RenameVectorTransform $ freshTransformSpaces n)
    SelectPos1L _ _ -> Right $ VPropPair (freshDBVSpace n) (uncurry RenameVectorTransform $ freshTransformSpaces n)
    ProjectRename (p1, p2) -> do
      ((D dis), (P pis)) <- unp is >>= fromDBV

      let src = case p2 of
            STDescrCol -> S dis
            STPosCol   -> S pis
            STNumber   -> S $ NumberDom pis

      let dst = case p1 of
            STDescrCol -> T dis
            STPosCol   -> T pis
            STNumber   -> T $ NumberDom pis

      Right $ VProp $ RenameVectorTransform src dst

    ProjectPayload _ -> Right is
    CompExpr1L _ -> Right is

    ProjectAdmin (descrProj, posProj) -> do
      (dis, (P pis)) <- unp is >>= fromDBV
      let dis' = case descrProj of
            DescrConst _  -> D $ freshSpace n "d"
            DescrIdentity -> dis
            DescrPosCol   -> D pis
      let pis' = case posProj of
            PosNumber   -> P $ NumberDom pis
            PosConst _  -> P $ freshSpace n "p"
            PosIdentity -> P pis
      return $ VProp $ DBVSpace dis' pis'

    SelectExpr _ -> do
      ((D dis), (P pis)) <- unp is >>= fromDBV
      let dis' = makeSubDomain n "d" dis
          pis' = makeSubDomain n "p" pis
      return $ VProp $ DBVSpace (D dis') (P pis')
    Only -> undefined
    Singleton -> undefined


    R1 ->
      case is of
        VPropPair s1 _ -> Right $ VProp s1
        VPropTriple s1 _ _ -> Right $ VProp s1
        _ -> Left "IndexSpace: Input of R1 is not a tuple"
    R2 ->
      case is of
        VPropPair _ s2 -> Right $ VProp s2
        VPropTriple _ s2 _ -> Right $ VProp s2
        _ -> Left "IndexSpace: Input of R2 is not a tuple"
    R3 ->
      case is of
        VPropTriple _ _ s3 -> Right $ VProp s3
        _ -> Left "IndexSpace: Input of R3 is not a tuple"

inferIndexSpaceBinOp :: VectorProp IndexSpace
                        -> VectorProp IndexSpace
                        -> AlgNode
                        -> BinOp
                        -> Either String (VectorProp IndexSpace)
inferIndexSpaceBinOp is1 is2 n op =
  case op of
    GroupBy ->
      let ddis = D $ freshSpace n "d/d"
          dpis = P $ freshSpace n "d/p"
          vdis = D $ freshSpace n "v/d"
          vpis = P $ freshSpace n "v/p"
          dv   = DescrVectorSpace ddis dpis
          dbv  = DBVSpace vdis vpis
          pv   = uncurry PropVectorTransform $ freshTransformSpaces n
      in Right $ VPropTriple dv dbv pv

    SortWith ->
      let ddis = D $ freshSpace n "d/d"
          dpis = P $ freshSpace n "d/p"
          vdis = D $ freshSpace n "v/d"
          vpis = P $ freshSpace n "v/p"
          dv   = DescrVectorSpace ddis dpis
          dbv  = DBVSpace vdis vpis
      in Right $ VPropPair dv dbv

    LengthSeg -> do
      (_, (P pis1)) <- unp is1 >>= fromDBV
      ((D dis2), _) <- unp is2 >>= fromDBV
      -- if the inner descriptor is a subdomain of the outer positions,
      -- the descriptor of the result is just the outer positions.
      -- This property holds because LengthSeg uses the outer positions
      -- to fill out any gaps in the inner descriptor.
      if dis2 `subDomain` pis1
        then return $ VProp $ DBVSpace (D pis1) (P $ freshSpace n "p")
        else return $ VProp $ freshDBVSpace n

    DistPrim -> Right $ uncurry VPropPair $ freshValuePropPair n
    DistDesc -> Right $ uncurry VPropPair $ freshValuePropPair n
    DistLift -> Right $ uncurry VPropPair $ freshValuePropPair n

    PropRename -> do
      (_, (T tis)) <- unp is1 >>= fromRenameVector
      (_, (P pis)) <- unp is2 >>= fromDBV
      return $ VProp $ DBVSpace (D tis) (P pis)

    PropFilter -> Right $ uncurry VPropPair $ freshValueRenamePair n
    PropReorder -> Right $ uncurry VPropPair $ freshValuePropPair n
    Append ->
      let d1sis = S $ freshSpace n "d1/s"
          d1tis = T $ freshSpace n "d1/t"
          d2sis = S $ freshSpace n "d2/s"
          d2tis = T $ freshSpace n "d2/t"
          d1v   = RenameVectorTransform d1sis d1tis
          d2v   = RenameVectorTransform d2sis d2tis
      in Right $ VPropTriple (freshDBVSpace n) d1v d2v
    RestrictVec -> Right $ uncurry VPropPair $ freshValueRenamePair n
    CompExpr2 _ -> Right $ VProp $ freshDBVSpace n
    CompExpr2L _ -> Right $ VProp $ freshDBVSpace n
    VecSumL -> Right $ VProp $ freshDBVSpace n
    SelectPos _ -> Right $ uncurry VPropPair $ freshValueRenamePair n
    SelectPosL _ -> Right $ uncurry VPropPair $ freshValueRenamePair n
    PairA -> Right $ VProp $ DBPSpace $ P $ freshSpace n "p"
    PairL -> Right $ VProp $ freshDBVSpace n

    ZipL ->
      let d1sis = S $ freshSpace n "d1/s"
          d1tis = T $ freshSpace n "d1/t"
          d2sis = S $ freshSpace n "d2/s"
          d2tis = T $ freshSpace n "d2/t"
          d1v   = RenameVectorTransform d1sis d1tis
          d2v   = RenameVectorTransform d2sis d2tis
      in Right $ VPropTriple (freshDBVSpace n) d1v d2v

    -- FIXME d \in p(q1)
    CartProduct -> Right $ VPropTriple (freshDBVSpace n) (freshPropSpace n) (freshPropSpace n)

    ThetaJoin _ -> do
      ((D dis), (P pis)) <- unp is1 >>= fromDBV
      let -- descr: descriptor of the left input on the first output
          dis'  = D $ makeSubDomain n "d" dis
          -- descr: positions of the left input on the second output
          dis'' = D $ makeSubDomain n "d" pis
          pis'  = P $ freshSpace n "p"
      Right $ VPropPair (DBVSpace dis' pis') (DBVSpace dis'' pis')


inferIndexSpaceTerOp :: VectorProp IndexSpace
                        -> VectorProp IndexSpace
                        -> VectorProp IndexSpace
                        -> AlgNode
                        -> TerOp
                        -> Either String (VectorProp IndexSpace)
inferIndexSpaceTerOp _ _ _ n op =
  case op of
    CombineVec ->
      let d1sis = S $ freshSpace n "d1/s"
          d1tis = T $ freshSpace n "d1/t"
          d2sis = S $ freshSpace n "d2/s"
          d2tis = T $ freshSpace n "d2/t"
          d1v   = RenameVectorTransform d1sis d1tis
          d2v   = RenameVectorTransform d2sis d2tis
      in Right $ VPropTriple (freshDBVSpace n) d1v d2v
