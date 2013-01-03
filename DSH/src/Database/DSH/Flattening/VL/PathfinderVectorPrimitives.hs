{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Flattening.VL.PathfinderVectorPrimitives() where

import           Data.Maybe

import           Control.Applicative                         hiding (Const)

import           Control.Monad.State

import qualified Database.Algebra.VL.Data                    as VL
import           Database.DSH.Flattening.Common.Impossible
import qualified Database.DSH.Flattening.FKL.Data.FKL        as FKL
import           Database.DSH.Flattening.VL.Data.DBVector
import           Database.DSH.Flattening.VL.VectorPrimitives

import           Database.Algebra.Dag.Builder
import           Database.Algebra.Pathfinder

-- | Results are stored in column:
pos, item', item, descr, descr', descr'', pos', pos'', pos''', posold, posnew, ordCol, resCol, tmpCol, tmpCol' :: AttrName
pos       = "pos"
item      = "item1"
item'     = "item99999991"
descr     = "iter"
descr'    = "item99999501"
descr''   = "item99999502"
pos'      = "item99999601"
pos''     = "item99999602"
pos'''    = "item99999603"
posold    = "item99999604"
posnew    = "item99999605"
ordCol    = "item99999801"
resCol    = "item99999001"
tmpCol    = "item99999002"
tmpCol'   = "item99999003"


type ExprComp r a = StateT Int (GraphM r PFAlgebra) a

freshCol :: ExprComp r AttrName
freshCol = do
  i <- get
  put $ i + 1
  return $ "item" ++ (show i)

runExprComp :: ExprComp r a -> GraphM r PFAlgebra a
runExprComp m = evalStateT m 1000000000

algConstType :: VL.VLVal -> ATy
algConstType (VL.VLInt _)    = AInt
algConstType (VL.VLNat _)    = ANat
algConstType (VL.VLBool _)   = ABool
algConstType (VL.VLString _) = AStr
algConstType (VL.VLDouble _) = ADouble
algConstType VL.VLUnit       = ANat

compileExpr1' :: AlgNode -> VL.Expr1 -> ExprComp r (AlgNode, AttrName)
compileExpr1' n (VL.App1 op e1 e2)   = do
  col      <- freshCol
  (n1, c1) <- compileExpr1' n e1
  (n2, c2) <- compileExpr1' n1 e2
  -- FIXME certain operators (<= etc.) need to be implemented in a
  -- special way
  nr <- lift $ oper (show op) col c1 c2 n2
  return (nr, col)
compileExpr1' n (VL.Column1 dbcol)   = return (n, itemi dbcol)
compileExpr1' n (VL.Constant1 constVal) = do
  col <- freshCol
  let ty  = algConstType constVal
      val = algVal constVal
  nr <- lift $ attach col ty val n
  return (nr, col)

compileExpr1 :: AlgNode -> VL.Expr1 -> GraphM r PFAlgebra (AlgNode, AttrName)
compileExpr1 n e = runExprComp (compileExpr1' n e)

compileExpr2' :: AlgNode -> VL.Expr2 -> ExprComp r (AlgNode, AttrName)
compileExpr2' n (VL.App2 op e1 e2)         = do
  col <- freshCol
  (n1, c1) <- compileExpr2' n e1
  (n2, c2) <- compileExpr2' n1 e2
  nr <- lift $ oper (show op) col c1 c2 n2
  return (nr, col)
compileExpr2' n (VL.Column2Left (VL.L c))  = return (n, itemi c)
compileExpr2' n (VL.Column2Right (VL.R c)) = return (n, itemi' c)
compileExpr2' n (VL.Constant2 constVal)    = do
  col <- freshCol
  let ty  = algConstType constVal
      val = algVal constVal
  nr <- lift $ attach col ty val n
  return (nr, col)

compileExpr2 :: AlgNode -> VL.Expr2 -> GraphM r PFAlgebra (AlgNode, AttrName)
compileExpr2 n e = runExprComp (compileExpr2' n e)

instance VectorAlgebra PFAlgebra where

  compExpr1 expr (DBV q _) = do
    (qr, cr) <- compileExpr1 q expr
    qp <- proj [colP descr, colP pos, (item, cr)] qr
    return $ DBV qp [1]

  compExpr2 expr (DBP q1 _) (DBP q2 cols2) = do
    q <- applyBinExpr (length cols2) expr q1 q2
    return $ DBP q [1]

  compExpr2L expr (DBV q1 _) (DBV q2 cols2) = do
    q <- applyBinExpr (length cols2) expr q1 q2
    return $ DBV q [1]

  pairA (DBP q1 cols1) (DBP q2 cols2) = do
    (r, cols') <- doZip (q1, cols1) (q2, cols2)
    return $ DBP r cols'

  pairL (DBV q1 cols1) (DBV q2 cols2) = do
    (r, cols') <- doZip (q1, cols1) (q2, cols2)
    return $ DBV r cols'

  constructLiteralTable tys [] = do
    qr <- emptyTable ((descr, natT):(pos, natT):[(itemi i, algTy t) | (i, t) <- zip [1..] tys])
    return $ DBV qr [1..length tys]

  constructLiteralTable tys vs = do
    qr <- flip litTable' ((descr, natT):(pos, natT):[(itemi i, algTy t) | (i, t) <- zip [1..] tys])
                                 $ map (map algVal) vs
    return $ DBV qr [1..length tys]

  constructLiteralValue t v = (\(DBV v' cols) -> DBP v' cols) <$> constructLiteralTable t [v]

  integerToDoubleA (DBP q _) = do
    qr <- projM [colP descr, colP pos, (item, resCol)]
            $ cast item resCol doubleT q
    return $ DBP qr [1]

  integerToDoubleL (DBV q _) = do
    qr <- projM [colP descr, colP pos, (item, resCol)]
            $ cast item resCol doubleT q
    return $ DBV qr [1]

  projectA (DBP q _) pc = do
    qr <- tagM "projectA"
            $ proj ([colP descr, colP pos] ++ [(itemi n, itemi c) | (c, n) <- zip pc [1..] ]) q
    return $ DBP qr [1..length pc]

  projectL (DBV q _) pc = do
    qr <- tagM "projectL"
            $ proj ([colP descr, colP pos] ++ [(itemi n, itemi c) | (c, n) <- zip pc [1..] ]) q
    return $ DBV qr [1..length pc]

  propRename (RenameVector q1) (DBV q2 cols) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    q <- tagM "propRename"
           $ projM (pf [(descr, posnew), colP pos])
           $ eqJoin posold descr q1 q2
    return $ DBV q cols

  propFilter (RenameVector q1) (DBV q2 cols) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    q <- rownumM pos' [posnew, pos] Nothing $ eqJoin posold descr q1 q2
    qr1 <- flip DBV cols <$> proj (pf [(descr, posnew), (pos, pos')]) q
    qr2 <- RenameVector <$> proj [(posold, pos), (posnew, pos')] q
    return $ (qr1, qr2)

  -- For Pathfinder algebra, the filter and reorder cases are the same, since
  -- numbering to generate positions is done with a rownum and involves sorting.
  propReorder (PropVector q1) e2 = do
    (p, (RenameVector r)) <- propFilter (RenameVector q1) e2
    return (p, PropVector r)

  restrictVec (DBV q1 cols) (DBV qm _) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    q <- rownumM pos'' [pos] Nothing
           $ selectM resCol
           $ eqJoinM pos pos' (return q1)
           $ proj [(pos', pos), (resCol, item)] qm
    qr <- flip DBV cols <$> proj (pf [(pos, pos''), colP descr]) q
    qp <- RenameVector <$> proj [(posold, pos), (posnew, pos'')] q
    return $ (qr, qp)

  combineVec (DBV qb _) (DBV q1 cols) (DBV q2 _) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    d1 <- projM [colP pos', colP pos]
            $ rownumM pos' [pos] Nothing
            $ select item qb
    d2 <- projM [colP pos', colP pos]
          $ rownumM pos' [pos] Nothing
          $ selectM resCol
          $ notC resCol item qb
    q <- eqJoinM pos' posold (return d1) (proj (pf [(posold, pos), colP descr]) q1)
         `unionM`
         eqJoinM pos' posold (return d2) (proj (pf [(posold, pos), colP descr]) q2)
    qr <- flip DBV cols <$> proj (pf [colP descr, colP pos]) q
    qp1 <- RenameVector <$> proj [(posnew, pos), (posold, pos')] d1
    qp2 <- RenameVector <$> proj [(posnew, pos), (posold, pos')] d2
    return $ (qr, qp1, qp2)

  segment (DBV q cols) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    flip DBV cols <$> proj (pf [(descr, pos), colP pos]) q

  unsegment (DBV q cols) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    flip DBV cols <$> (attachM descr natT (nat 1) $ proj (pf [colP pos]) q)

  toDescr (DBV n _) = DescrVector <$> tagM "toDescr" (proj [colP descr, colP pos] n)

  notPrim (DBP q _) = flip DBP [1] <$> (projM [colP pos, colP descr, (item, tmpCol)] $ notC tmpCol item q)

  notVec (DBV d _) = flip DBV [1] <$> (projM [colP pos, colP descr, (item, tmpCol)] $ notC tmpCol item d)

  distPrim (DBP q1 cols) (DescrVector q2) = do
    qr <- crossM (proj [(itemi i, itemi i) | i <- cols] q1) (return q2)
    r <- proj [(posnew, pos), (posold, descr)] q2
    return (DBV qr cols, PropVector r)

  distDesc (DBV q1 cols) (DescrVector q2) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols ]
    q <- projM (pf [(descr, pos), (pos, pos''), (posold, posold)])
           $ rownumM pos'' [pos, pos'] Nothing
           $ crossM
               (proj [colP pos] q2)
               (proj (pf [(pos', pos), (posold, pos)]) q1)
    qr1 <- flip DBV cols <$> proj (pf [colP descr, colP pos]) q
    qr2 <- PropVector <$> proj [(posold, posold), (posnew, pos)] q
    return $ (qr1, qr2)

  distLift (DBV q1 cols) (DescrVector q2) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    q <- eqJoinM pos' descr (proj (pf [(pos', pos)]) q1) $ return q2
    qr1 <- flip DBV cols <$> proj (pf [colP descr, colP pos]) q
    qr2 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] q
    return $ (qr1, qr2)

  lengthA (DescrVector d) = do
    qr <- attachM descr natT (nat 1)
            $ attachM pos natT (nat 1)
            $ aggrM [(Max, item, Just item)] Nothing
            $ (litTable (int 0) item intT)
              `unionM`
              (aggrM [(Count, item, Nothing)] Nothing $ proj [colP pos] d)
    return $ DBP qr [1]

  lengthSeg (DescrVector q1) (DescrVector d) = do
    qr <- rownumM pos [descr] Nothing
            $ aggrM [(Max, item, Just item)] (Just descr)
            $ (attachM item intT (int 0) $ proj [(descr, pos)] q1)
              `unionM`
              (aggrM [(Count, item, Nothing)] (Just descr) $ proj [colP descr] d)
    return $ DBV qr [1]

  reverseA (DBV q cols) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    q' <- rownum' pos' [(pos, Desc)] Nothing q
    r <- flip DBV cols <$> proj (pf [colP descr, (pos, pos')]) q'
    p <- PropVector <$> proj [(posold, pos), (posnew, pos')] q'
    return (r, p)

  reverseL (DBV q cols) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    q' <- rownum' pos' [(descr, Asc), (pos, Desc)] Nothing q
    r <- flip DBV cols <$> proj (pf [colP descr, (pos, pos')]) q'
    p <- PropVector <$> proj [(posold, pos), (posnew, pos')] q'
    return (r, p)

  unique (DBV q cols) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    f <- rownumM posnew [posold] Nothing
           $ aggrM [(Min, posold, Just pos)] (Just resCol)
           $ rank resCol [(itemi i, Asc) | i <- cols] q

    flip DBV cols <$> (projM (pf [colP descr, (pos, posnew)]) $ eqJoin pos posold q f)

  uniqueL (DBV q cols) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    f <- rownumM posnew [posold] Nothing
           $ aggrM [(Min, posold, Just pos)] (Just resCol)
           $ rank resCol ((descr, Asc):[(itemi i, Asc) | i <- cols]) q
    flip DBV cols <$> (projM (pf [colP descr, (pos, posnew)]) $ eqJoin pos posold q f)

  vecMin (DBV q _) = do
    qr <- attachM descr natT (nat 1)
            $ attachM pos natT (nat 1)
            $ aggr [(Min, item, Just item)] Nothing q
    return $ DBP qr [1]

  vecMax (DBV q _) = do
    qr <- attachM descr natT (nat 1)
            $ attachM pos natT (nat 1)
            $ aggr [(Max, item, Just item)] Nothing q
    return $ DBP qr [1]

  vecMinLift (DBV qv _) = do
    qr <- projM [colP descr,colP pos,colP item]
            $ rownumM pos [descr] Nothing
            $ aggr [(Min, item, Just item)] (Just descr) qv
    return $ DBV qr [1]

  vecMaxLift (DBV qv _) = do
    qr <- projM [colP descr,colP pos,colP item]
            $ rownumM pos [descr] Nothing
            $ aggr [(Max, item, Just item)] (Just descr) qv
    return $ DBV qr [1]

  descToRename (DescrVector q1) = RenameVector <$> proj [(posnew, descr), (posold, pos)] q1

  singletonDescr = DescrVector <$> (attachM pos natT (nat 1) $ litTable (nat 1) descr natT)

  append (DBV q1 cols) (DBV q2 _) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    q <- rownumM pos' [descr, ordCol, pos] Nothing
           $ attach ordCol natT (nat 1) q1
             `unionM`
             attach ordCol natT (nat 2) q2
    qv <- flip DBV cols <$> tagM "append r" (proj (pf [(pos, pos'), colP descr]) q)
    qp1 <- RenameVector <$> (tagM "append r1"
                        $ projM [(posold, pos), (posnew, pos')]
                        $ selectM resCol
                        $ operM "==" resCol ordCol tmpCol
                        $ attach tmpCol natT (nat 1) q)
    qp2 <- RenameVector <$> (tagM "append r2"
                        $ projM [(posold, pos), (posnew, pos')]
                        $ selectM resCol
                        $ operM "==" resCol ordCol tmpCol
                        $ attach tmpCol natT (nat 2) q)
    return $ (qv, qp1, qp2)

  vecSum t (DBV q _) = do
    -- the default value for empty lists
    q' <- attachM pos natT (nat 1)
            $ attachM descr natT (nat 1)
            $ case t of
                VL.Int -> litTable (int 0) item intT
                VL.Nat -> litTable (nat 0) item natT
                VL.Double -> litTable (double 0) item doubleT
                _   -> error "This type is not supported by the sum primitive (PF)"
    -- the actual sum
    qs <- attachM descr natT (nat 1)
         $ attachM pos natT (nat 1)
         $ aggrM [(Sum, item, Just item)] Nothing
         $ union q' q
    return $ DBP qs [1]

  vecSumLift (DescrVector qd) (DBV qv _) = do
    qe <- attachM item intT (int 0) -- TODO: In general you do not know that it should be an int, it might be double or nat...
          $ differenceM
            (proj [(descr, pos)] qd)
            (proj [colP descr] qv)
    qs <- aggr [(Sum, item, Just item)] (Just descr) qv
    qr <- rownumM pos [descr] Nothing
          $ union qe qs
    -- align the result vector with the original descriptor vector to get
    -- the proper descriptor values (sum removes one list type constructor)
    qa <- projM [(descr, descr'), colP pos, (item, item)]
          $ (eqJoinM pos' descr
             (proj [(descr', descr), (pos', pos)] qd)
             (return qr))
    return $ DBV qa [1]

  selectExpr expr (DBV q cols) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    (qe, ce) <- compileExpr1 q expr
    qr <- projM (pf [colP descr, colP pos])
          $ eqJoinM pos pos'
              (return q)
              (proj [(pos', pos), colP ce] qe)
    return $ DBV qr cols

  -- FIXME CHECK BARRIER operator implementations above this line have been checked
  -- to conform to the X100 implementations

  groupBy = groupByPF

  tableRef = tableRefPF
  sortWith = sortWithPF
  selectPos = selectPosPF
  selectPos1 = undefined
  selectPosLift = selectPosLiftPF
  selectPos1Lift = undefined

  zipL = undefined


  falsePositions = undefined

  cartProduct = undefined

  thetaJoin = undefined


  projectRename = undefined

  projectPayload = undefined
  projectAdmin = undefined

colP :: AttrName -> (AttrName, AttrName)
colP a = (a, a)

doZip :: (AlgNode, [DBCol]) -> (AlgNode, [DBCol]) -> GraphM r PFAlgebra (AlgNode, [DBCol])
doZip (q1, cols1) (q2, cols2) = do
  let offset = length cols1
  let cols' = cols1 ++ map (+offset) cols2
  r <- projM (colP descr : colP pos : map (colP . itemi) cols')
         $ eqJoinM pos pos'
           (return q1)
           (proj ((pos', pos):[ (itemi $ i + offset, itemi i) | i <- cols2 ]) q2)
  return (r, cols')

selectPosLiftPF :: DBV -> VL.VecCompOp -> DBV -> GraphM r PFAlgebra (DBV, RenameVector)
selectPosLiftPF (DBV qe cols) op (DBV qi _) =
    do
        let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
        qx <- castM pos' pos''' intT
                $ eqJoinM descr pos''
                    (rownum pos' [pos] (Just descr) qe)
                    (proj [(pos'', pos), (item', item)] qi)
        qs <- case op of
            VL.LtE -> rownumM posnew [descr, pos] Nothing
                  $ selectM resCol
                  $ unionM
                    (oper (show VL.Eq) resCol pos''' item' qx)
                    (oper (show VL.Lt) resCol pos''' item' qx)
            _ -> rownumM posnew [descr, pos] Nothing
                  $ selectM resCol
                  $ oper (show op) resCol pos''' item' qx
        q <- proj (pf [colP descr, (pos, posnew)]) qs
        qp <- proj [(posold, pos), (posnew, posnew)] qs
        return $ (DBV q cols, RenameVector qp)

selectPosPF :: DBV -> VL.VecCompOp -> DBP -> GraphM r PFAlgebra (DBV, RenameVector)
selectPosPF (DBV qe cols) op (DBP qi _) =
    do
        let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
        qx <- crossM
                (projM (pf [colP descr, colP pos']) (cast pos pos' intT qe))
                -- (proj (pf [colP descr, (pos', pos)]) qe)
                (proj [(item', item)] qi)
        qn <- case op of
                VL.Lt ->
                    projM (pf [colP descr, (pos, pos'), colP pos'])
                     $ selectM resCol
                           $ oper (show op) resCol pos' item' qx
                VL.LtE ->
                    projM (pf [colP descr, (pos, pos'), colP pos'])
                     $ selectM resCol
                        $ unionM
                            (oper (show VL.Lt) resCol pos' item' qx)
                            (oper (show VL.Eq) resCol pos' item' qx)
                _ ->
                    projM (pf [colP descr, colP pos, colP pos'])
                     $ rownumM pos [descr, pos'] Nothing
                        $ selectM resCol
                            $ oper (show op) resCol pos' item' qx
        q <- proj (pf [colP descr, colP pos]) qn
        qp <- proj [(posnew, pos), (posold, pos')] qn
        return $ (DBV q cols, RenameVector qp)






applyBinOp :: VL.VecOp -> AlgNode -> AlgNode -> GraphM r PFAlgebra AlgNode
applyBinOp op q1 q2 =
  projM [(item, resCol), colP descr, colP pos]
    $ operM (show op) resCol item tmpCol
    $ eqJoinM pos pos' (return q1)
    $ proj [(tmpCol, item), (pos', pos)] q2

applyBinExpr :: Int -> VL.Expr2 -> AlgNode -> AlgNode -> GraphM r PFAlgebra AlgNode
applyBinExpr rightWidth e q1 q2 = do
  let colShift = [ (itemi' i, itemi i) | i <- [1..rightWidth] ]
  qCombined <- eqJoinM pos pos' (return q1)
               -- shift the column names on the rigth to avoid name collisions
               $ proj ((pos', pos) : colShift) q2
  (qr, cr) <- compileExpr2 qCombined e
  proj [colP descr, colP pos, (item, cr)] qr

binOpLPF :: VL.VecOp -> DBV -> DBV -> GraphM r PFAlgebra DBV
binOpLPF op (DBV q1 _) (DBV q2 _) | op == (VL.COp VL.GtE) = do
                                             q1' <- applyBinOp (VL.COp VL.Gt) q1 q2
                                             q2' <- applyBinOp (VL.COp VL.Eq) q1 q2
                                             flip DBV [1] <$> applyBinOp (VL.BOp VL.Disj) q1' q2'
                              | op == (VL.COp VL.LtE) = do
                                             q1' <- applyBinOp (VL.COp VL.Lt) q1 q2
                                             q2' <- applyBinOp (VL.COp VL.Eq) q1 q2
                                             flip DBV [1] <$> applyBinOp (VL.BOp VL.Disj) q1' q2'
                              | otherwise = flip DBV [1] <$> applyBinOp op q1 q2

binOpPF :: VL.VecOp -> DBP -> DBP -> GraphM r PFAlgebra DBP
binOpPF op (DBP q1 _) (DBP q2 _) | op == (VL.COp VL.GtE) = do
                                            q1' <- applyBinOp (VL.COp VL.Gt) q1 q2
                                            q2' <- applyBinOp (VL.COp VL.Eq) q1 q2
                                            flip DBP [1] <$> applyBinOp (VL.BOp VL.Disj) q1' q2'
                             | op == (VL.COp VL.LtE) = do
                                           q1' <- applyBinOp (VL.COp VL.Lt) q1 q2
                                           q2' <- applyBinOp (VL.COp VL.Eq) q1 q2
                                           flip DBP [1] <$> applyBinOp (VL.BOp VL.Disj) q1' q2'
                             | otherwise = flip DBP [1] <$> applyBinOp op q1 q2

sortWithPF :: DBV -> DBV -> GraphM r PFAlgebra (DBV, PropVector)
sortWithPF (DBV qs colss) (DBV qe colse) =
    do
        let pf = \x -> x ++ [(itemi i, itemi i) | i <- colse]
        q <- tagM "sortWith"
             $ eqJoinM pos pos''
               (projM [colP pos, colP pos']
                $ rownum pos' (descr : [itemi i | i <- colss] ++ [pos]) Nothing qs)
               (proj (pf [colP descr, (pos'', pos)]) qe)
        qv <- proj (pf [colP descr, (pos, pos')]) q
        qp <- proj [(posold, pos''), (posnew, pos')] q
        return $ (DBV qv colse, PropVector qp)

groupByPF :: DBV -> DBV -> GraphM r PFAlgebra (DescrVector, DBV, PropVector)
groupByPF (DBV v1 colsg) (DBV v2 colse) = do
                                             q' <- rownumM pos' [resCol, pos] Nothing $ rowrank resCol ((descr, Asc):[(itemi i, Asc) | i<- colsg]) v1
                                             d1 <- distinctM $ proj [colP descr, (pos, resCol)] q'
                                             p <- proj [(posold, pos), (posnew, pos')] q'
                                             v <- tagM "groupBy ValueVector" $ projM [colP descr, colP pos, (item, item)]
                                                    $ eqJoinM pos'' pos' (proj [(descr, resCol), (pos, pos'), (pos'', pos)] q')
                                                                         (proj ((pos', pos):[(itemi i, itemi i) | i <- colse]) v2)
                                             return $ (DescrVector d1, DBV v colse, PropVector p)











itemi :: Int -> AttrName
itemi i = "item" ++ show i

itemi' :: Int -> AttrName
itemi' i = "item" ++ show i ++ "x"

algVal :: VL.VLVal -> AVal
algVal (VL.VLInt i) = int (fromIntegral i)
algVal (VL.VLBool t) = bool t
algVal VL.VLUnit = int (-1)
algVal (VL.VLString s) = string s
algVal (VL.VLDouble d) = double d
algVal (VL.VLNat n) = nat $ fromIntegral n

algTy :: VL.VLType -> ATy
algTy (VL.Int) = intT
algTy (VL.Double) = doubleT
algTy (VL.Bool) = boolT
algTy (VL.String) = stringT
algTy (VL.Unit) = intT
algTy (VL.Nat) = natT
algTy (VL.Pair _ _) = $impossible
algTy (VL.VLList _) = $impossible

tableRefPF :: String -> [VL.TypedColumn] -> [FKL.Key] -> GraphM r PFAlgebra DBV
tableRefPF n cs ks = do
                     table <- dbTable n (renameCols cs) keyItems
                     t' <- attachM descr natT (nat 1) $ rownum pos (head keyItems) Nothing table
                     cs' <- tagM "table" $ proj (colP descr:colP pos:[(itemi i, itemi i) | i <- [1..length cs]]) t'
                     return $ DBV cs' [1..length cs]
  where
    renameCols :: [VL.TypedColumn] -> [Column]
    renameCols xs = [NCol cn [Col i $ algTy t] | ((cn, t), i) <- zip xs [1..]]
    numberedCols = zip cs [1 :: Integer .. ]
    numberedColNames = map (\(c, i) -> (fst c, i)) numberedCols
    keyItems = map (map (\c -> "item" ++ (show $ fromJust $ lookup c numberedColNames))) ks

