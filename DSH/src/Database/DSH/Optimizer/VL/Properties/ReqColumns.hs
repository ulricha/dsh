{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Properties.ReqColumns where

import           Control.Applicative
import qualified Data.List as L
import qualified Data.List.NonEmpty as N

import           Database.DSH.VL.Lang
import           Database.DSH.Optimizer.VL.Properties.Types


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

reqExpr1Cols :: Expr1 -> [DBCol]
reqExpr1Cols (BinApp1 _ e1 e2) = reqExpr1Cols e1 `L.union` reqExpr1Cols e2
reqExpr1Cols (UnApp1 _ e)      = reqExpr1Cols e
reqExpr1Cols (Column1 col)     = [col]
reqExpr1Cols (Constant1 _)     = []

reqExpr2ColsLeft :: Expr2 -> [DBCol]
reqExpr2ColsLeft (BinApp2 _ e1 e2)     = reqExpr2ColsLeft e1 `L.union` reqExpr2ColsLeft e2
reqExpr2ColsLeft (UnApp2 _ e)          = reqExpr2ColsLeft e
reqExpr2ColsLeft (Column2Left (L col)) = [col]
reqExpr2ColsLeft (Column2Right _)      = []
reqExpr2ColsLeft (Constant2 _)         = []

reqExpr2ColsRight :: Expr2 -> [DBCol]
reqExpr2ColsRight (BinApp2 _ e1 e2)      = reqExpr2ColsRight e1 `L.union` reqExpr2ColsRight e2
reqExpr2ColsRight (UnApp2 _ e)           = reqExpr2ColsRight e
reqExpr2ColsRight (Column2Right (R col)) = [col]
reqExpr2ColsRight (Column2Left _)        = []
reqExpr2ColsRight (Constant2 _)          = []

aggrReqCols :: AggrFun -> [DBCol]
aggrReqCols (AggrSum _ e) = reqExpr1Cols e
aggrReqCols (AggrMin e)   = reqExpr1Cols e
aggrReqCols (AggrMax e)   = reqExpr1Cols e
aggrReqCols (AggrAvg e)   = reqExpr1Cols e
aggrReqCols AggrCount     = []

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
        rightReqCols = cols `L.intersect` [(w1 + 1) .. (w1 + w2)]
    return (VProp $ Just leftReqCols, VProp $ Just rightReqCols)

-- | Infer required columns for unary operators
inferReqColumnsUnOp :: BottomUpProps          -- ^ Input properties
                    -> VectorProp ReqCols     -- ^ Columns required from the current node
                    -> VectorProp ReqCols     -- ^ Columns required from the input node
                    -> UnOp                   -- ^ Current operator
                    -> Either String (VectorProp ReqCols)
inferReqColumnsUnOp childBUProps ownReqColumns childReqColumns op =
    case op of
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
    
        DescToRename -> none ∪ childReqColumns
    
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
    
        Reverse    -> ownReqColumns ∪ childReqColumns
        ReverseS   -> ownReqColumns ∪ childReqColumns
    
        Project ps -> childReqColumns ∪ (VProp $ Just $ L.nub $ concatMap reqExpr1Cols ps)
    
        Select e   -> do
            ownReqColumns' <- ownReqColumns ∪ (VProp $ Just $ reqExpr1Cols e)
            ownReqColumns' ∪ childReqColumns
    
        SelectPos1 _ _   -> do
            cols <- fst <$> fromPropPair ownReqColumns
            childReqColumns ∪ (VProp cols)
    
        SelectPos1S _ _   -> do
            cols <- fst <$> fromPropPair ownReqColumns
            childReqColumns ∪ (VProp cols)
            
        -- We don't need to look at the columns required from above,
        -- because they can only be a subset of (gs ++ as).
        GroupAggr gs as -> childReqColumns 
                           ∪ 
                           (VProp $ Just $ L.nub $ concatMap reqExpr1Cols gs 
                                                   ++ 
                                                   concatMap aggrReqCols (N.toList as))
    
        SortSimple exprs -> do
            ownReqColumns' <- ownReqColumns 
                              ∪ 
                              (VProp $ Just $ L.nub $ concatMap reqExpr1Cols exprs)
            childReqColumns ∪ ownReqColumns'
    
        GroupSimple exprs -> do
            ownReqColumns' <- ownReqColumns 
                              ∪ 
                              (VProp $ Just $ L.nub $ concatMap reqExpr1Cols exprs)
            childReqColumns ∪ ownReqColumns'
    
        R1               ->
            case childReqColumns of
                VProp _                       -> fail $ "ReqColumns.R1 " ++ (show childReqColumns)
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
    
        Only      -> childReqColumns ∪ ownReqColumns
        Singleton -> childReqColumns ∪ ownReqColumns


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
      GroupBy         -> do
          (_, cols, _)  <- fromPropTriple ownReqColumns
          colsFromLeft  <- allCols childBUProps1
          colsFromRight <- childReqColumns2 ∪ (VProp cols)
          return (colsFromLeft, colsFromRight)
  
      Sort            -> do
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
  
      AggrNonEmptyS aggrFuns -> do
          fromLeft  <- childReqColumns1 ∪ none 
          fromRight <- (VProp $ Just 
                              $ concatMap aggrReqCols (N.toList aggrFuns))
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
  
      DistSeg -> do
          cols      <- fst <$> fromPropPair ownReqColumns
          fromLeft  <- VProp cols ∪ childReqColumns1
          fromRight <- childReqColumns2 ∪ none
          return (fromLeft, fromRight)

      Align -> do
          cols <- fst <$> fromPropPair ownReqColumns
          (ownLeft, ownRight) <- partitionCols childBUProps1 childBUProps2 cols
          (,) <$> (childReqColumns1 ∪ ownLeft) <*> (childReqColumns2 ∪ ownRight)
          
      PropRename -> do
          fromRight <- childReqColumns2 ∪ ownReqColumns
          return (na, fromRight)
  
      PropFilter      -> do
          fromRight <- childReqColumns2 ∪ ownReqColumns
          return (na, fromRight)
  
      PropReorder -> do
          cols      <- fst <$> fromPropPair ownReqColumns
          fromRight <- childReqColumns2 ∪ VProp cols
          return (na, fromRight)
  
      Append -> do
          (cols, _, _) <- fromPropTriple ownReqColumns
          fromLeft     <- (VProp cols) ∪ childReqColumns1
          fromRight    <- (VProp cols) ∪ childReqColumns2
          return (fromLeft, fromRight)
  
      Restrict -> do
          cols     <- fst <$> fromPropPair ownReqColumns
          fromLeft <- VProp cols ∪ childReqColumns1
          return (fromLeft, one)
  
      BinExpr e -> do
          reqColsLeft  <- (VProp $ Just $ reqExpr2ColsLeft e) ∪ childReqColumns1
          reqColsRight <- (VProp $ Just $ reqExpr2ColsRight e) ∪ childReqColumns2
          return (reqColsLeft, reqColsRight)
  
      SelectPos _ -> do
          cols     <- fst <$> fromPropPair ownReqColumns
          fromLeft <- VProp cols ∪ childReqColumns1
          return (fromLeft, one)
  
      SelectPosS _ -> do
          cols     <- fst <$> fromPropPair ownReqColumns
          fromLeft <- VProp cols ∪ childReqColumns1
          return (fromLeft, one)
  
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
  
      EquiJoin le re -> do
          (cols1, _, _)               <- fromPropTriple ownReqColumns
          (leftReqCols, rightReqCols) <- partitionCols childBUProps1 childBUProps2 cols1
          leftReqCols'                <- (VProp $ Just $ reqExpr1Cols le) ∪ leftReqCols
          rightReqCols'               <- (VProp $ Just $ reqExpr1Cols re) ∪ rightReqCols
          (,) <$> (childReqColumns1 ∪ leftReqCols') <*> (childReqColumns2 ∪ rightReqCols')
  
      EquiJoinS le re -> do
          (cols1, _, _)               <- fromPropTriple ownReqColumns
          (leftReqCols, rightReqCols) <- partitionCols childBUProps1 childBUProps2 cols1
          leftReqCols'                <- (VProp $ Just $ reqExpr1Cols le) ∪ leftReqCols
          rightReqCols'               <- (VProp $ Just $ reqExpr1Cols re) ∪ rightReqCols
          (,) <$> (childReqColumns1 ∪ leftReqCols') <*> (childReqColumns2 ∪ rightReqCols')
  
      NestJoinS le re -> do
          cols1                       <- fst <$> fromPropPair ownReqColumns
          (leftReqCols, rightReqCols) <- partitionCols childBUProps1 childBUProps2 cols1
          leftReqCols'                <- (VProp $ Just $ reqExpr1Cols le) ∪ leftReqCols
          rightReqCols'               <- (VProp $ Just $ reqExpr1Cols re) ∪ rightReqCols
          (,) <$> (childReqColumns1 ∪ leftReqCols') <*> (childReqColumns2 ∪ rightReqCols')
  
      ZipS -> do
          (cols, _, _) <- fromPropTriple ownReqColumns
          (ownLeft, ownRight) <- partitionCols childBUProps1 childBUProps2 cols
          (,) <$> (childReqColumns1 ∪ ownLeft) <*> (childReqColumns2 ∪ ownRight)
      
      -- For a semijoin, we only require the columns used in the join argument
      -- from the right input.
      SemiJoin e1 e2 -> do
          cols1     <- fst <$> fromPropPair ownReqColumns
          fromLeft  <- ((VProp $ Just $ reqExpr1Cols e1) ∪ VProp cols1) >>= (∪ childReqColumns1)
          fromRight <- (VProp $ Just $ reqExpr1Cols e2) ∪ childReqColumns2
          return (fromLeft, fromRight)
  
      -- For a semijoin, we only require the columns used in the join argument
      -- from the right input.
      SemiJoinS e1 e2 -> do
          cols1     <- fst <$> fromPropPair ownReqColumns
          fromLeft  <- ((VProp $ Just $ reqExpr1Cols e1) ∪ VProp cols1) >>= (∪ childReqColumns1)
          fromRight <- (VProp $ Just $ reqExpr1Cols e2) ∪ childReqColumns2
          return (fromLeft, fromRight)
  
      -- For a antijoin, we only require the columns used in the join argument
      -- from the right input.
      AntiJoin e1 e2 -> do
          cols1     <- fst <$> fromPropPair ownReqColumns
          fromLeft  <- ((VProp $ Just $ reqExpr1Cols e1) ∪ VProp cols1) >>= (∪ childReqColumns1)
          fromRight <- (VProp $ Just $ reqExpr1Cols e2) ∪ childReqColumns2
          return (fromLeft, fromRight)
  
      -- For a antijoin, we only require the columns used in the join argument
      -- from the right input.
      AntiJoinS e1 e2 -> do
          cols1     <- fst <$> fromPropPair ownReqColumns
          fromLeft  <- ((VProp $ Just $ reqExpr1Cols e1) ∪ VProp cols1) >>= (∪ childReqColumns1)
          fromRight <- (VProp $ Just $ reqExpr1Cols e2) ∪ childReqColumns2
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
