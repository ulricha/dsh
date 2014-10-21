{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Properties.ReqColumns where

import           Control.Applicative
import qualified Data.List                                  as L
import qualified Data.List.NonEmpty                         as N

import           Database.DSH.Common.Lang
import           Database.DSH.Optimizer.VL.Properties.Types
import           Database.DSH.VL.Lang


(∪) :: VectorProp ReqCols -> VectorProp ReqCols -> Either String (VectorProp ReqCols)
(∪) (VProp (Just cols1)) (VProp (Just cols2)) = return $ VProp $ Just $ cols1 `L.union` cols2
(∪) (VProp (Just cols1)) (VProp Nothing)      = return $ VProp $ Just $ cols1
(∪) (VProp Nothing)      (VProp (Just cols2)) = return $ VProp $ Just $ cols2
(∪) (VProp Nothing)      (VProp Nothing)      = return $ VProp $ Nothing
(∪) p1                   p2                   = Left $ "ReqColumns.union"
                                                       ++ " "
                                                       ++ (show p1)
                                                       ++ " "
                                                       ++ (show p2)

none :: VectorProp ReqCols
none = VProp $ Just []

one :: VectorProp ReqCols
one = VProp $ Just [1]

na :: VectorProp ReqCols
na = VProp Nothing

reqExprCols :: Expr -> [DBCol]
reqExprCols (BinApp _ e1 e2) = reqExprCols e1 `L.union` reqExprCols e2
reqExprCols (UnApp _ e)      = reqExprCols e
reqExprCols (Column col)     = [col]
reqExprCols (Constant _)     = []
reqExprCols (If c t e)       = reqExprCols c `L.union` reqExprCols t `L.union` reqExprCols e

reqLeftPredCols :: JoinPredicate Expr -> [DBCol]
reqLeftPredCols (JoinPred cs) = L.nub 
                                $ concatMap (\(JoinConjunct le _ _) -> reqExprCols le) 
                                $ N.toList cs

reqRightPredCols :: JoinPredicate Expr -> [DBCol]
reqRightPredCols (JoinPred cs) = L.nub 
                                $ concatMap (\(JoinConjunct _ _ re) -> reqExprCols re) 
                                $ N.toList cs

aggrReqCols :: AggrFun -> [DBCol]
aggrReqCols (AggrSum _ e) = reqExprCols e
aggrReqCols (AggrMin e)   = reqExprCols e
aggrReqCols (AggrMax e)   = reqExprCols e
aggrReqCols (AggrAvg e)   = reqExprCols e
aggrReqCols (AggrAll e)   = reqExprCols e
aggrReqCols (AggrAny e)   = reqExprCols e
aggrReqCols AggrCount     = []

winReqCols :: WinFun -> [DBCol]
winReqCols (WinSum e)        = reqExprCols e
winReqCols (WinMin e)        = reqExprCols e
winReqCols (WinMax e)        = reqExprCols e
winReqCols (WinAvg e)        = reqExprCols e
winReqCols (WinAll e)        = reqExprCols e
winReqCols (WinAny e)        = reqExprCols e
winReqCols (WinFirstValue e) = reqExprCols e
winReqCols WinCount          = []

fromProp :: Show a => VectorProp a -> Either String a
fromProp (VProp p) = return p
fromProp x         = fail $ "ReqColumns.fromProp " ++ (show x)

fromPropPair :: VectorProp a -> Either String (a, a)
fromPropPair (VPropPair x y) = return (x, y)
fromPropPair _               = fail "not a property pair"

fromPropTriple :: VectorProp a -> Either String (a, a, a)
fromPropTriple (VPropTriple x y z) = return (x, y, z)
fromPropTriple _                   = fail "not a property triple"

allCols :: BottomUpProps -> Either String (VectorProp ReqCols)
allCols props = do
    VProp (ValueVector w) <- return $ vectorTypeProp props
    return $ VProp $ Just [1 .. w]

-- | For operators that combine two value vectors in a product-like
-- manner (products, joins, zips, ...), map the columns that are
-- required from above to the respective input columns.
partitionCols :: BottomUpProps   -- ^ Available columns in the left input
              -> BottomUpProps   -- ^ Available columns in the right input
              -> ReqCols         -- ^ Columns required from above
              -> Either String (VectorProp ReqCols, VectorProp ReqCols)
partitionCols childBUProps1 childBUProps2 ownReqCols = do
    ValueVector w1 <- fromProp $ vectorTypeProp childBUProps1
    ValueVector w2 <- fromProp $ vectorTypeProp childBUProps2

    let cols = maybe [] id ownReqCols

    -- If both inputs are ValueVectors, map the required columns to
    -- the respective inputs
    let leftReqCols  = cols `L.intersect` [1 .. w1]
        rightReqCols = map (\c -> c - w1) $ cols `L.intersect` [(w1 + 1) .. (w1 + w2)]
    return (VProp $ Just leftReqCols, VProp $ Just rightReqCols)

-- | Infer required columns for unary operators
inferReqColumnsUnOp :: BottomUpProps          -- ^ Input properties
                    -> VectorProp ReqCols     -- ^ Columns required from the current node
                    -> VectorProp ReqCols     -- ^ Columns required from the input node
                    -> UnOp                   -- ^ Current operator
                    -> Either String (VectorProp ReqCols)
inferReqColumnsUnOp childBUProps ownReqColumns childReqColumns op =
    case op of
        WinFun (wfun, _) -> do
            cs <- (VProp $ Just $ winReqCols wfun)
                  ∪
                  childReqColumns
            cs ∪ ownReqColumns
        Transpose  -> do
            cols <- snd <$> fromPropPair ownReqColumns
            childReqColumns ∪ VProp cols

        Reshape _  -> do
            cols <- snd <$> fromPropPair ownReqColumns
            VProp cols ∪ childReqColumns

        ReshapeS _ -> do
            cols <- snd <$> fromPropPair ownReqColumns
            VProp cols ∪ childReqColumns

        UniqueS    -> ownReqColumns ∪ childReqColumns

        Aggr aggrFun -> (VProp $ Just $ aggrReqCols aggrFun)
                        ∪
                        childReqColumns

        AggrNonEmpty aggrFuns -> (VProp $ Just $ concatMap aggrReqCols (N.toList aggrFuns))
                                 ∪
                                 childReqColumns

        UnboxRename -> none ∪ childReqColumns

        Segment    -> ownReqColumns ∪ childReqColumns
        Unsegment  -> ownReqColumns ∪ childReqColumns

        -- Numbering operators add one column at the end. We have to
        -- determine the column index of the new column and remove it
        -- from the set of required columns
        Number     -> do
            ValueVector w <- fromProp $ vectorTypeProp childBUProps
            Just cols     <- fromProp ownReqColumns
            let cols'     = filter (/= w) cols
            VProp (Just cols') ∪ childReqColumns
        NumberS    -> do
            ValueVector w <- fromProp $ vectorTypeProp childBUProps
            (Just cols)   <- fromProp ownReqColumns
            let cols'     = filter (/= w) cols
            VProp (Just cols') ∪ childReqColumns

        Reverse    -> do
            cols <- fst <$> fromPropPair ownReqColumns
            VProp cols ∪ childReqColumns
        ReverseS   -> do
            cols <- fst <$> fromPropPair ownReqColumns
            VProp cols ∪ childReqColumns

        Project ps -> childReqColumns ∪ (VProp $ Just $ L.nub $ concatMap reqExprCols ps)

        Select e   -> do
            cols           <- fst <$> fromPropPair ownReqColumns
            ownReqColumns' <- (VProp cols) ∪ (VProp $ Just $ reqExprCols e)
            ownReqColumns' ∪ childReqColumns

        SelectPos1{}   -> do
            (cols, _, _) <- fromPropTriple ownReqColumns
            childReqColumns ∪ (VProp cols)

        SelectPos1S{}   -> do
            (cols, _, _) <- fromPropTriple ownReqColumns
            childReqColumns ∪ (VProp cols)

        -- We don't need to look at the columns required from above,
        -- because they can only be a subset of (gs ++ as).
        GroupAggr (gs, as) -> childReqColumns
                           ∪
                           (VProp $ Just $ L.nub $ concatMap reqExprCols gs
                                                   ++
                                                   concatMap aggrReqCols (N.toList as))

        SortScalarS exprs -> do
            cols <- fst <$> fromPropPair ownReqColumns
            ownReqColumns' <- VProp cols
                              ∪
                              (VProp $ Just $ L.nub $ concatMap reqExprCols exprs)
            childReqColumns ∪ ownReqColumns'

        GroupScalarS exprs -> do
            (_, colsi, _) <- fromPropTriple ownReqColumns
            ownReqColumns' <- VProp colsi
                              ∪
                              (VProp $ Just $ L.nub $ concatMap reqExprCols exprs)
            childReqColumns ∪ ownReqColumns'

        AggrNonEmptyS aggrFuns -> do
          reqCols <- (VProp $ Just $ concatMap aggrReqCols (N.toList aggrFuns))
                      ∪
                      childReqColumns
          return reqCols

        R1               ->
            case childReqColumns of
                VProp _                       -> Left $ "ReqColumns.R1 " ++ (show childReqColumns)
                VPropPair cols1 cols2         -> do
                    cols1' <- fromProp =<< VProp cols1 ∪ ownReqColumns
                    return $ VPropPair cols1' cols2
                VPropTriple cols1 cols2 cols3 -> do
                    cols1' <- fromProp =<< VProp cols1 ∪ ownReqColumns
                    return $ VPropTriple cols1' cols2 cols3

        R2               ->
            case childReqColumns of
                VProp _                       -> fail "ReqColumns.R2"
                VPropPair cols1 cols2         -> do
                    cols2' <- fromProp =<< VProp cols2 ∪ ownReqColumns
                    return $ VPropPair cols1 cols2'
                VPropTriple cols1 cols2 cols3 -> do
                    cols2' <- fromProp =<< VProp cols2 ∪ ownReqColumns
                    return $ VPropTriple cols1 cols2' cols3

        R3               ->
            case childReqColumns of
                VProp _                       -> fail "ReqColumns.R3/1"
                VPropPair _ _                 -> fail "ReqColumns.R3/2"
                VPropTriple cols1 cols2 cols3 -> do
                    cols3' <- fromProp =<< VProp cols3 ∪ ownReqColumns
                    return $ VPropTriple cols1 cols2 cols3'


-- | Infer required columns for binary operators
inferReqColumnsBinOp :: BottomUpProps
                     -> BottomUpProps
                     -> VectorProp ReqCols
                     -> VectorProp ReqCols
                     -> VectorProp ReqCols
                     -> BinOp
                     -> Either String (VectorProp ReqCols, VectorProp ReqCols)
inferReqColumnsBinOp childBUProps1 childBUProps2 ownReqColumns childReqColumns1 childReqColumns2 op =
  case op of
      Group         -> do
          (_, cols, _)  <- fromPropTriple ownReqColumns
          colsFromLeft  <- allCols childBUProps1
          colsFromRight <- childReqColumns2 ∪ (VProp cols)
          return (colsFromLeft, colsFromRight)

      SortS            -> do
          cols          <- fst <$> fromPropPair ownReqColumns
          colsFromLeft  <- allCols childBUProps1
          colsFromRight <- childReqColumns2 ∪ (VProp cols)
          return (colsFromLeft, colsFromRight)

      AggrS aggrFun   -> do
          fromLeft  <- childReqColumns1 ∪ none
          fromRight <- (VProp $ Just $ aggrReqCols aggrFun)
                       ∪
                       childReqColumns2
          return (fromLeft, fromRight)

      DistPrim -> do
          cols <- fst <$> fromPropPair ownReqColumns
          (,) <$> (childReqColumns1 ∪ VProp cols) <*> (childReqColumns2 ∪ none)

      DistDesc -> do
          cols      <- fst <$> fromPropPair ownReqColumns
          fromLeft  <- VProp cols ∪ childReqColumns1
          fromRight <- childReqColumns2 ∪ none
          return (fromLeft, fromRight)

      DistLift -> do
          cols <- fst <$> fromPropPair ownReqColumns
          (ownLeft, ownRight) <- partitionCols childBUProps1 childBUProps2 cols
          (,) <$> (childReqColumns1 ∪ ownLeft) <*> (childReqColumns2 ∪ ownRight)

      PropRename -> do
          fromRight <- childReqColumns2 ∪ ownReqColumns
          return (na, fromRight)

      PropFilter      -> do
          cols      <- fst <$> fromPropPair ownReqColumns
          fromRight <- childReqColumns2 ∪ VProp cols
          return (na, fromRight)

      PropReorder -> do
          cols      <- fst <$> fromPropPair ownReqColumns
          fromRight <- childReqColumns2 ∪ VProp cols
          return (na, fromRight)

      UnboxNested -> do
          cols      <- fst <$> fromPropPair ownReqColumns
          fromRight <- childReqColumns2 ∪ VProp cols
          return (na, fromRight)

      Append -> do
          (cols, _, _) <- fromPropTriple ownReqColumns
          fromLeft     <- (VProp cols) ∪ childReqColumns1
          fromRight    <- (VProp cols) ∪ childReqColumns2
          return (fromLeft, fromRight)

      AppendS -> do
          (cols, _, _) <- fromPropTriple ownReqColumns
          fromLeft     <- (VProp cols) ∪ childReqColumns1
          fromRight    <- (VProp cols) ∪ childReqColumns2
          return (fromLeft, fromRight)

      SelectPos _ -> do
          (cols, _, _) <- fromPropTriple ownReqColumns
          fromLeft     <- VProp cols ∪ childReqColumns1
          return (fromLeft, one)

      SelectPosS _ -> do
          (cols, _, _) <- fromPropTriple ownReqColumns
          fromLeft     <- VProp cols ∪ childReqColumns1
          return (fromLeft, one)

      Align -> do
          cols <- fromProp ownReqColumns
          (ownLeft, ownRight) <- partitionCols childBUProps1 childBUProps2 cols
          (,) <$> (childReqColumns1 ∪ ownLeft) <*> (childReqColumns2 ∪ ownRight)

      Zip -> do
          cols <- fromProp ownReqColumns
          (ownLeft, ownRight) <- partitionCols childBUProps1 childBUProps2 cols
          (,) <$> (childReqColumns1 ∪ ownLeft) <*> (childReqColumns2 ∪ ownRight)

      CartProduct -> do
          (cols1, _, _)       <- fromPropTriple ownReqColumns
          (ownLeft, ownRight) <- partitionCols childBUProps1 childBUProps2 cols1
          (,) <$> (childReqColumns1 ∪ ownLeft) <*> (childReqColumns2 ∪ ownRight)

      CartProductS -> do
          (cols1, _, _)       <- fromPropTriple ownReqColumns
          (ownLeft, ownRight) <- partitionCols childBUProps1 childBUProps2 cols1
          (,) <$> (childReqColumns1 ∪ ownLeft) <*> (childReqColumns2 ∪ ownRight)

      NestProductS -> do
          cols1 <- fst <$> fromPropPair ownReqColumns
          (ownLeft, ownRight) <- partitionCols childBUProps1 childBUProps2 cols1
          (,) <$> (childReqColumns1 ∪ ownLeft) <*> (childReqColumns2 ∪ ownRight)

      ThetaJoin p -> do
          (cols1, _, _)               <- fromPropTriple ownReqColumns
          (leftReqCols, rightReqCols) <- partitionCols childBUProps1 childBUProps2 cols1
          leftReqCols'                <- (VProp $ Just $ reqLeftPredCols p) ∪ leftReqCols
          rightReqCols'               <- (VProp $ Just $ reqRightPredCols p) ∪ rightReqCols
          (,) <$> (childReqColumns1 ∪ leftReqCols') <*> (childReqColumns2 ∪ rightReqCols')

      UnboxScalar -> do
          cols1                       <- fromProp ownReqColumns
          (leftReqCols, rightReqCols) <- partitionCols childBUProps1 childBUProps2 cols1
          (,) <$> (childReqColumns1 ∪ leftReqCols) <*> (childReqColumns2 ∪ rightReqCols)

      NestJoin p -> do
          (cols1, _, _)               <- fromPropTriple ownReqColumns
          (leftReqCols, rightReqCols) <- partitionCols childBUProps1 childBUProps2 cols1
          leftReqCols'                <- (VProp $ Just $ reqLeftPredCols p) ∪ leftReqCols
          rightReqCols'               <- (VProp $ Just $ reqRightPredCols p) ∪ rightReqCols
          (,) <$> (childReqColumns1 ∪ leftReqCols') <*> (childReqColumns2 ∪ rightReqCols')

      ThetaJoinS p -> do
          (cols1, _, _)               <- fromPropTriple ownReqColumns
          (leftReqCols, rightReqCols) <- partitionCols childBUProps1 childBUProps2 cols1
          leftReqCols'                <- (VProp $ Just $ reqLeftPredCols p) ∪ leftReqCols
          rightReqCols'               <- (VProp $ Just $ reqRightPredCols p) ∪ rightReqCols
          (,) <$> (childReqColumns1 ∪ leftReqCols') <*> (childReqColumns2 ∪ rightReqCols')

      NestJoinS p -> do
          cols1                       <- fst <$> fromPropPair ownReqColumns
          (leftReqCols, rightReqCols) <- partitionCols childBUProps1 childBUProps2 cols1
          leftReqCols'                <- (VProp $ Just $ reqLeftPredCols p) ∪ leftReqCols
          rightReqCols'               <- (VProp $ Just $ reqRightPredCols p) ∪ rightReqCols
          (,) <$> (childReqColumns1 ∪ leftReqCols') <*> (childReqColumns2 ∪ rightReqCols')

      ZipS -> do
          (cols, _, _) <- fromPropTriple ownReqColumns
          (ownLeft, ownRight) <- partitionCols childBUProps1 childBUProps2 cols
          (,) <$> (childReqColumns1 ∪ ownLeft) <*> (childReqColumns2 ∪ ownRight)

      -- For a semijoin, we only require the columns used in the join argument
      -- from the right input.
      SemiJoin p -> do
          cols1     <- fst <$> fromPropPair ownReqColumns
          fromLeft  <- ((VProp $ Just $ reqLeftPredCols p) ∪ VProp cols1) >>= (∪ childReqColumns1)
          fromRight <- (VProp $ Just $ reqRightPredCols p) ∪ childReqColumns2
          return (fromLeft, fromRight)

      -- For a semijoin, we only require the columns used in the join argument
      -- from the right input.
      SemiJoinS p -> do
          cols1     <- fst <$> fromPropPair ownReqColumns
          fromLeft  <- ((VProp $ Just $ reqLeftPredCols p) ∪ VProp cols1) >>= (∪ childReqColumns1)
          fromRight <- (VProp $ Just $ reqRightPredCols p) ∪ childReqColumns2
          return (fromLeft, fromRight)

      -- For a antijoin, we only require the columns used in the join argument
      -- from the right input.
      AntiJoin p -> do
          cols1     <- fst <$> fromPropPair ownReqColumns
          fromLeft  <- ((VProp $ Just $ reqLeftPredCols p) ∪ VProp cols1) >>= (∪ childReqColumns1)
          fromRight <- (VProp $ Just $ reqRightPredCols p) ∪ childReqColumns2
          return (fromLeft, fromRight)

      -- For a antijoin, we only require the columns used in the join argument
      -- from the right input.
      AntiJoinS p -> do
          cols1     <- fst <$> fromPropPair ownReqColumns
          fromLeft  <- ((VProp $ Just $ reqLeftPredCols p) ∪ VProp cols1) >>= (∪ childReqColumns1)
          fromRight <- (VProp $ Just $ reqRightPredCols p) ∪ childReqColumns2
          return (fromLeft, fromRight)

      TransposeS -> do
          cols      <- snd <$> fromPropPair ownReqColumns
          fromRight <- childReqColumns2 ∪ VProp cols
          return (none, fromRight)

inferReqColumnsTerOp :: VectorProp ReqCols
                     -> VectorProp ReqCols
                     -> VectorProp ReqCols
                     -> VectorProp ReqCols
                     -> TerOp
                     -> Either String (VectorProp ReqCols, VectorProp ReqCols, VectorProp ReqCols)
inferReqColumnsTerOp ownReqColumns _ childReqColumns2 childReqColumns3 op =
    case op of
        Combine -> do
            (cols, _, _) <- fromPropTriple ownReqColumns
            fromLeft     <- VProp cols ∪ childReqColumns2
            fromRight    <- VProp cols ∪ childReqColumns3
            return (one, fromLeft, fromRight)
