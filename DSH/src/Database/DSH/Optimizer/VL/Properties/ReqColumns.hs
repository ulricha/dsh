module Database.DSH.Optimizer.VL.Properties.ReqColumns where

import qualified Data.List as L
import           Database.Algebra.VL.Data
import Database.DSH.Optimizer.VL.Properties.Types

unp :: Show a => VectorProp a -> a
unp (VProp x) = x
unp x         = error $ "ReqColumns.unp " ++ (show x)

union :: VectorProp ReqCols -> VectorProp ReqCols -> VectorProp ReqCols
union (VProp (Just cols1)) (VProp (Just cols2)) = VProp $ Just $ cols1 `L.union` cols2
union (VProp (Just cols1)) (VProp Nothing)      = VProp $ Just $ cols1
union (VProp Nothing)      (VProp (Just cols2)) = VProp $ Just $ cols2
union (VProp Nothing)      (VProp Nothing)      = VProp $ Nothing
union p1                   p2                   = error ("ReqColumns.union" ++ " " ++ (show p1) ++ " " ++ (show p2))

none :: VectorProp ReqCols
none = VProp $ Just []

one :: VectorProp ReqCols
one = VProp $ Just [1]

na :: VectorProp ReqCols
na = VProp Nothing

reqExpr1Cols :: Expr1 -> [DBCol]
reqExpr1Cols (App1 _ e1 e2) = reqExpr1Cols e1 `L.union` reqExpr1Cols e2
reqExpr1Cols (Column1 col)  = [col]
reqExpr1Cols (Constant1 _)  = []

reqExpr2ColsLeft :: Expr2 -> [DBCol]
reqExpr2ColsLeft (App2 _ e1 e2)        = reqExpr2ColsLeft e1 `L.union` reqExpr2ColsLeft e2
reqExpr2ColsLeft (Column2Left (L col)) = [col]
reqExpr2ColsLeft (Column2Right _)      = []
reqExpr2ColsLeft (Constant2 _)         = []

reqExpr2ColsRight :: Expr2 -> [DBCol]
reqExpr2ColsRight (App2 _ e1 e2)         = reqExpr2ColsRight e1 `L.union` reqExpr2ColsRight e2
reqExpr2ColsRight (Column2Right (R col)) = [col]
reqExpr2ColsRight (Column2Left _)        = []
reqExpr2ColsRight (Constant2 _)          = []

allCols :: BottomUpProps -> VectorProp ReqCols
allCols props = case vectorTypeProp props of
                 (VProp (ValueVector w)) -> VProp $ Just [1 .. w]
                 _                       -> error "ReqColumns.allCols: ValueVector expected"

partitionCols :: BottomUpProps -> BottomUpProps -> ReqCols -> (VectorProp ReqCols, VectorProp ReqCols)
partitionCols childBUProps1 childBUProps2 ownReqCols =
  let childType1 = unp $ vectorTypeProp childBUProps1
      childType2 = unp $ vectorTypeProp childBUProps2
  in
   case ownReqCols of
     Just cols ->
       case (childType1, childType2) of
         -- If both inputs are ValueVectors, map the required columns to the respective inputs
         (ValueVector w1, ValueVector w2) ->
           let leftReqCols  = cols `L.intersect` [1 .. w1]
               rightReqCols = cols `L.intersect` [(w1 + 1) .. (w1 + w2)]
           in (VProp $ Just leftReqCols, VProp $ Just rightReqCols)
         _                                -> error ("partitionCols " ++ (show childType1) ++ " " ++ (show childType2))
     Nothing -> (na, na)

inferReqColumnsUnOp :: VectorProp ReqCols
                -> VectorProp ReqCols
                -> UnOp
                -> VectorProp ReqCols
inferReqColumnsUnOp ownReqColumns childReqColumns op =
  case op of
    Unique -> ownReqColumns `union` childReqColumns

    UniqueL -> ownReqColumns `union` childReqColumns

    NotPrim -> one

    NotVec -> one

    LengthA -> none `union` childReqColumns

    DescToRename -> none `union` childReqColumns

    Segment -> ownReqColumns `union` childReqColumns
    Unsegment -> ownReqColumns `union` childReqColumns

    VecSum _ -> one
    VecAvg -> one
    VecMin -> one
    VecMinL -> one
    VecMax -> one
    VecMaxL -> one
    
    Number -> none
    NumberL -> none

    IntegerToDoubleA -> one
    IntegerToDoubleL -> one

    ReverseA -> ownReqColumns `union` childReqColumns
    ReverseL -> ownReqColumns `union` childReqColumns

    FalsePositions -> one

    ProjectRename _ -> none `union` childReqColumns

    VLProject ps -> childReqColumns `union` (VProp $ Just $ L.nub $ concatMap reqExpr1Cols ps)
    VLProjectA ps -> childReqColumns `union` (VProp $ Just $ L.nub $ concatMap reqExpr1Cols ps)

    ProjectAdmin _ -> ownReqColumns `union` childReqColumns

    SelectExpr e -> childReqColumns `union` (VProp $ Just $ reqExpr1Cols e)

    CompExpr1L e -> childReqColumns `union` (VProp $ Just $ reqExpr1Cols e)

    SelectPos1 _ _   ->
      case ownReqColumns of
        VPropPair cols _ -> childReqColumns `union` (VProp cols)
        _                -> error "SelectPos1"

    SelectPos1L _ _   ->
      case ownReqColumns of
        VPropPair cols _ -> childReqColumns `union` (VProp cols)
        _                -> error "SelectPos1L"
        
    -- We don't need to look at the columns required from above, because they
    -- can only be a subset of (gs ++ as).
    VecAggr gs as -> childReqColumns `union` (VProp $ Just $ L.nub $ gs ++ concatMap aggrInputCol as)

      where aggrInputCol :: AggrFun -> [DBCol]
            aggrInputCol (Max c) = [c]
            aggrInputCol (Min c) = [c]
            aggrInputCol (Sum c) = [c]
            aggrInputCol (Avg c) = [c]
            aggrInputCol Count   = []

    R1               ->
      case childReqColumns of
        VProp _                       -> error $ "ReqColumns.R1 " ++ (show childReqColumns)
        VPropPair cols1 cols2         -> VPropPair (unp (union (VProp cols1) ownReqColumns)) cols2
        VPropTriple cols1 cols2 cols3 -> VPropTriple (unp (union (VProp cols1) ownReqColumns)) cols2 cols3

    R2               ->
      case childReqColumns of
        VProp _              -> error "ReqColumns.R2"
        VPropPair cols1 cols2      -> VPropPair cols1 (unp (union (VProp cols2) ownReqColumns))
        VPropTriple cols1 cols2 cols3 -> VPropTriple cols1 (unp (union (VProp cols2) ownReqColumns)) cols3
    R3               ->
      case childReqColumns of
        VProp _              -> error "ReqColumns.R3/1"
        VPropPair _ _        -> error "ReqColumns.R3/2"
        VPropTriple cols1 cols2 cols3 -> VPropTriple cols1 cols2 (unp (union (VProp cols3) ownReqColumns))

    Only -> undefined
    Singleton -> undefined


inferReqColumnsBinOp :: BottomUpProps
                        -> BottomUpProps
                        -> VectorProp ReqCols
                        -> VectorProp ReqCols
                        -> VectorProp ReqCols
                        -> BinOp
                        -> (VectorProp ReqCols, VectorProp ReqCols)
inferReqColumnsBinOp childBUProps1 childBUProps2 ownReqColumns childReqColumns1 childReqColumns2 op =
  case op of
    GroupBy         ->
      case ownReqColumns of
        VPropTriple _ cols _ -> (allCols childBUProps1, childReqColumns2 `union` (VProp cols))
        _                    -> undefined -- FIXME

    SortWith        ->
      case ownReqColumns of
        VPropPair cols _  -> (allCols childBUProps1, union childReqColumns2 (VProp cols))
        _                 -> undefined -- FIXME

    LengthSeg -> (childReqColumns1 `union` none, childReqColumns2 `union` none)

    DistPrim -> (childReqColumns1 `union` ownReqColumns, childReqColumns2 `union` none)

    DistDesc ->
      case ownReqColumns of
        VPropPair cols _ -> ((VProp cols) `union` childReqColumns1, childReqColumns2 `union` none)
        _                -> error "DistDesc"

    DistLift ->
      case ownReqColumns of
        VPropPair cols _ -> ((VProp cols) `union` childReqColumns1, childReqColumns2 `union` none)
        _                -> error "DistLift"

    PropRename      -> (na, childReqColumns2 `union` ownReqColumns)

    PropFilter      ->
      case ownReqColumns of
        VPropPair cols _ -> (na, childReqColumns2 `union` (VProp cols))
        _                -> error "PropFilter"

    PropReorder ->
      case ownReqColumns of
        VPropPair cols _ -> (na, (VProp cols) `union` childReqColumns2)
        _                -> error "PropReorder"

    Append ->
      case ownReqColumns of
        VPropTriple cols _ _ -> (union (VProp cols) childReqColumns1, union (VProp cols) childReqColumns2)
        _                    -> error "Append"

    RestrictVec ->
      case ownReqColumns of
        VPropPair cols _ -> (union (VProp cols) childReqColumns1, one)
        _                -> error "RestrictVec"

    CompExpr2 e ->
      let reqColsLeft  = (VProp $ Just $ reqExpr2ColsLeft e) `union` childReqColumns1
          reqColsRight = (VProp $ Just $ reqExpr2ColsRight e) `union` childReqColumns2
      in (reqColsLeft, reqColsRight)

    CompExpr2L e ->
      let reqColsLeft  = (VProp $ Just $ reqExpr2ColsLeft e) `union` childReqColumns1
          reqColsRight = (VProp $ Just $ reqExpr2ColsRight e) `union` childReqColumns2
      in (reqColsLeft, reqColsRight)

    VecSumL -> (childReqColumns1 `union` none, one)
    VecAvgL -> (childReqColumns1 `union` none, one)

    SelectPos _ ->
      case ownReqColumns of
        VPropPair cols _ -> ((VProp cols) `union` childReqColumns1, one)
        _                -> error "SelectPos"
    SelectPosL _ ->
      case ownReqColumns of
        VPropPair cols _ -> ((VProp cols) `union` childReqColumns1, one)
        _                -> error "SelectPosL"

    PairA -> partitionCols childBUProps1 childBUProps2 (unp ownReqColumns)

    PairL -> partitionCols childBUProps1 childBUProps2 (unp ownReqColumns)

    CartProduct ->
      case ownReqColumns of
        VPropTriple cols1 _ _ -> partitionCols childBUProps1 childBUProps2 cols1
        _                     -> error "ReqColumns.CartProduct"

    CartProductL ->
      case ownReqColumns of
        VPropTriple cols1 _ _ -> partitionCols childBUProps1 childBUProps2 cols1
        _                     -> error "ReqColumns.CartProduct"

    EquiJoin le re ->
      case ownReqColumns of
        VPropTriple cols1 _ _ -> 
          let (leftReqCols, rightReqCols) = partitionCols childBUProps1 childBUProps2 cols1
              leftReqCols'  = union (VProp $ Just $ reqExpr1Cols le) leftReqCols
              rightReqCols' = union (VProp $ Just $ reqExpr1Cols re) rightReqCols
          in (leftReqCols', rightReqCols')
        _                     -> error "ReqColumns.EquiJoin"

    EquiJoinL le re ->
      case ownReqColumns of
        VPropTriple cols1 _ _ -> 
          let (leftReqCols, rightReqCols) = partitionCols childBUProps1 childBUProps2 cols1
              leftReqCols'  = union (VProp $ Just $ reqExpr1Cols le) leftReqCols
              rightReqCols' = union (VProp $ Just $ reqExpr1Cols re) rightReqCols
          in (leftReqCols', rightReqCols')
        _                     -> error "ReqColumns.EquiJoinL"

    -- FIXME recheck for correctness
    ZipL -> partitionCols childBUProps1 childBUProps2 (unp ownReqColumns) 
    
    -- For a semijoin, we only require the columns used in the join argument
    -- from the right input.
    SemiJoin e1 e2 -> 
      case ownReqColumns of
        VPropPair cols1 _ -> 
          (union (VProp $ Just $ reqExpr1Cols e1) (VProp cols1), VProp $ Just $ reqExpr1Cols e2)
        _                     -> error "ReqColumns.SemiJoin"

    -- For a semijoin, we only require the columns used in the join argument
    -- from the right input.
    SemiJoinL e1 e2 -> 
      case ownReqColumns of
        VPropPair cols1 _ -> 
          (union (VProp $ Just $ reqExpr1Cols e1) (VProp cols1), VProp $ Just $ reqExpr1Cols e2)
        _                     -> error "ReqColumns.SemiJoinL"

    -- For a antijoin, we only require the columns used in the join argument
    -- from the right input.
    AntiJoin e1 e2 -> 
      case ownReqColumns of
        VPropPair cols1 _ -> 
          (union (VProp $ Just $ reqExpr1Cols e1) (VProp cols1), VProp $ Just $ reqExpr1Cols e2)
        _                     -> error "ReqColumns.AntiJoin"

    -- For a antijoin, we only require the columns used in the join argument
    -- from the right input.
    AntiJoinL e1 e2 -> 
      case ownReqColumns of
        VPropPair cols1 _ -> 
          (union (VProp $ Just $ reqExpr1Cols e1) (VProp cols1), VProp $ Just $ reqExpr1Cols e2)
        _                     -> error "ReqColumns.AntiJoinL"
    
    

inferReqColumnsTerOp :: VectorProp ReqCols
                 -> VectorProp ReqCols
                 -> VectorProp ReqCols
                 -> VectorProp ReqCols
                 -> TerOp
                 -> (VectorProp ReqCols, VectorProp ReqCols, VectorProp ReqCols)
inferReqColumnsTerOp ownReqColumns _ childReqColumns2 _ op =
  case op of
    CombineVec ->
      case ownReqColumns of
        VPropTriple cols _ _ -> (one, union (VProp cols) childReqColumns2, union (VProp cols) childReqColumns2)
        _                    -> error "CombineVec"
