{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VL.PathfinderVectorPrimitives() where
       
import           Debug.Trace

import           Data.Maybe

import           Control.Applicative                         hiding (Const)

import           Control.Monad.State

import qualified Database.Algebra.VL.Data                    as VL
import           Database.DSH.Impossible
import           Database.DSH.VL.Data.DBVector
import           Database.DSH.VL.VectorPrimitives

import           Database.Algebra.Dag.Builder
import           Database.Algebra.Pathfinder
import           Database.Algebra.Pathfinder.Data.Algebra

-- Some general helpers

-- | Results are stored in column:
pos, item', item, descr, descr', descr'', pos', pos'', pos''', posold, posnew, ordCol, resCol, tmpCol, tmpCol' :: AttrName
pos       = "pos"
item      = "item1"
item'     = "itemtmp"
descr     = "iter"
descr'    = "iter1"
descr''   = "iter2"
pos'      = "pos1"
pos''     = "pos2"
pos'''    = "pos3"
posold    = "posold"
posnew    = "posnew"
ordCol    = "ord"
resCol    = "res"
tmpCol    = "tmp1"
tmpCol'   = "tmp2"

itemi :: Int -> AttrName
itemi i = "item" ++ show i

itemi' :: Int -> AttrName
itemi' i = "itemtmp" ++ show i

exprcoli :: Int -> AttrName
exprcoli i = "expr" ++ show i

algVal :: VL.VLVal -> AVal
algVal (VL.VLInt i) = int (fromIntegral i)
algVal (VL.VLBool t) = bool t
algVal VL.VLUnit = int (-1)
algVal (VL.VLString s) = string s
algVal (VL.VLDouble d) = double d
algVal (VL.VLNat n) = nat $ fromIntegral n

algConstType :: VL.VLVal -> ATy
algConstType (VL.VLInt _)    = AInt
algConstType (VL.VLNat _)    = ANat
algConstType (VL.VLBool _)   = ABool
algConstType (VL.VLString _) = AStr
algConstType (VL.VLDouble _) = ADouble
algConstType VL.VLUnit       = ANat

algTy :: VL.VLType -> ATy
algTy (VL.Int) = intT
algTy (VL.Double) = doubleT
algTy (VL.Bool) = boolT
algTy (VL.String) = stringT
algTy (VL.Unit) = intT
algTy (VL.Nat) = natT
algTy (VL.Pair _ _) = $impossible
algTy (VL.VLList _) = $impossible

colP :: AttrName -> (AttrName, AttrName)
colP a = (a, a)

transProj :: AttrName -> VL.ISTransProj -> (AttrName, AttrName)
transProj target VL.STPosCol   = (target, pos)
transProj target VL.STDescrCol = (target, descr)
transProj _      VL.STNumber   = $impossible

keepItems :: [DBCol] -> (ProjInf -> ProjInf)
keepItems cols projs = projs ++ [ colP $ itemi i | i <- cols ]

algOp :: VL.VecOp -> Fun
algOp (VL.NOp VL.Add)  = Fun1to1 Plus
algOp (VL.NOp VL.Sub)  = Fun1to1 Minus
algOp (VL.NOp VL.Div)  = Fun1to1 Times
algOp (VL.NOp VL.Mul)  = Fun1to1 Div
algOp (VL.NOp VL.Mod)  = Fun1to1 Modulo
algOp (VL.COp VL.Eq)   = RelFun Eq
algOp (VL.COp VL.Gt)   = RelFun Gt
algOp (VL.COp VL.GtE)  = $impossible
algOp (VL.COp VL.Lt)   = RelFun Lt
algOp (VL.COp VL.LtE)  = $impossible
algOp (VL.BOp VL.Conj) = RelFun And
algOp (VL.BOp VL.Disj) = RelFun Or
algOp VL.Like          = Fun1to1 Like

unOp :: VL.VecUnOp -> (AttrName -> AttrName -> AlgNode -> GraphM a PFAlgebra AlgNode)
unOp VL.Not                    = notC
unOp (VL.CastOp VL.CastDouble) = \resCol argCol q -> cast resCol argCol ADouble q

algCompOp :: VL.VecCompOp -> Fun
algCompOp VL.Eq = RelFun Eq
algCompOp VL.Gt = RelFun Gt
algCompOp _     = $impossible
          
aggrFun :: VL.AggrFun -> AggrType
aggrFun (VL.AggrSum c) = Sum $ itemi c
aggrFun (VL.AggrMin c) = Min $ itemi c
aggrFun (VL.AggrMax c) = Max $ itemi c
aggrFun (VL.AggrAvg c) = Avg $ itemi c
aggrFun VL.AggrCount   = Count

-- Compilation of VL expressions (Expr1, Expr2)

type ExprComp r a = StateT Int (GraphM r PFAlgebra) a

freshCol :: ExprComp r AttrName
freshCol = do
  i <- get
  put $ i + 1
  return $ exprcoli i
  
runExprComp :: ExprComp r a -> GraphM r PFAlgebra a
runExprComp m = evalStateT m 1

specialComparison :: AlgNode -> AttrName -> AttrName -> Fun -> ExprComp r (AlgNode, AttrName)
specialComparison n leftArg rightArg op = do
  opCol    <- freshCol
  opNode   <- lift $ oper op opCol leftArg rightArg n
  eqCol    <- freshCol
  eqNode   <- lift $ oper (RelFun Eq) eqCol leftArg rightArg opNode
  orCol    <- freshCol
  andNode  <- lift $ oper (RelFun Or) orCol opCol eqCol eqNode
  return (andNode, orCol)

compileExpr1' :: [DBCol] -> AlgNode -> VL.Expr1 -> ExprComp r (AlgNode, AttrName)
compileExpr1' cols n (VL.BinApp1 (VL.COp VL.LtE) e1 e2) = do
  (n1, c1) <- compileExpr1' cols n e1
  (n2, c2) <- compileExpr1' cols n1 e2
  specialComparison n2 c1 c2 (RelFun Lt)
compileExpr1' cols n (VL.BinApp1 (VL.COp VL.GtE) e1 e2) = do
  (n1, c1) <- compileExpr1' cols n e1
  (n2, c2) <- compileExpr1' cols n1 e2
  specialComparison n2 c1 c2 (RelFun Lt)

compileExpr1' cols n (VL.BinApp1 op e1 e2)   = do
  col      <- freshCol
  (n1, c1) <- compileExpr1' cols n e1
  (n2, c2) <- compileExpr1' cols n1 e2
  nr <- lift $ oper (algOp op) col c1 c2 n2
  return (nr, col)

compileExpr1' cols n (VL.UnApp1 op e) = do
  col <- freshCol
  (n', c) <- compileExpr1' cols n e
  nr <- lift $ unOp op col c n'
  return (nr, col)

compileExpr1' _ n (VL.Column1 dbcol)      = return (n, itemi dbcol)
compileExpr1' _ n (VL.Constant1 constVal) = do
  col <- freshCol
  let ty  = algConstType constVal
      val = algVal constVal
  nr <- lift $ attach col ty val n
  return (nr, col)

compileExpr1 :: [DBCol] -> AlgNode -> VL.Expr1 -> GraphM r PFAlgebra (AlgNode, AttrName)
compileExpr1 cols n e = runExprComp (compileExpr1' cols n e)
             
compileExpr2' :: AlgNode -> VL.Expr2 -> ExprComp r (AlgNode, AttrName)
compileExpr2' n (VL.BinApp2 (VL.COp VL.LtE) e1 e2) = do
  (n1, c1) <- compileExpr2' n e1
  (n2, c2) <- compileExpr2' n1 e2
  specialComparison n2 c1 c2 (RelFun Lt)

compileExpr2' n (VL.BinApp2 (VL.COp VL.GtE) e1 e2) = do
  (n1, c1) <- compileExpr2' n e1
  (n2, c2) <- compileExpr2' n1 e2
  specialComparison n2 c1 c2 (RelFun Lt)

compileExpr2' n (VL.BinApp2 op e1 e2)         = do
  col <- freshCol
  (n1, c1) <- compileExpr2' n e1
  (n2, c2) <- compileExpr2' n1 e2
  nr <- lift $ oper (algOp op) col c1 c2 n2
  return (nr, col)
compileExpr2' n (VL.UnApp2 op e)              = do
  col <- freshCol
  (n', c) <- compileExpr2' n e
  nr <- lift $ unOp op col c n'
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

-- Common building blocks

doZip :: (AlgNode, [DBCol]) -> (AlgNode, [DBCol]) -> GraphM r PFAlgebra (AlgNode, [DBCol])
doZip (q1, cols1) (q2, cols2) = do
  let offset = length cols1
  let cols' = cols1 ++ map (+offset) cols2
  r <- projM (colP descr : colP pos : map (colP . itemi) cols')
         $ eqJoinM pos pos'
           (return q1)
           (proj ((pos', pos):[ (itemi $ i + offset, itemi i) | i <- cols2 ]) q2)
  return (r, cols')

applyBinExpr :: Int -> VL.Expr2 -> AlgNode -> AlgNode -> GraphM r PFAlgebra AlgNode
applyBinExpr rightWidth e q1 q2 = do
  let colShift = [ (itemi' i, itemi i) | i <- [1..rightWidth] ]
  qCombined <- eqJoinM pos pos' (return q1)
               -- shift the column names on the right to avoid name collisions
               $ proj ((pos', pos) : colShift) q2
  (qr, cr) <- compileExpr2 qCombined e
  proj [colP descr, colP pos, (item, cr)] qr

doProject :: [VL.Expr1] -> AlgNode -> GraphM r PFAlgebra AlgNode
doProject projs q = do
    let mkProj :: [VL.Expr1]
               -> [(AttrName, AttrName)]
               -> Int
               -> AlgNode
               -> GraphM r PFAlgebra ([(AttrName, AttrName)], AlgNode)
        mkProj (e : es) projections colIndex q' = do
            (qr, c) <- compileExpr1 [1..colIndex] q' e
            mkProj es ((itemi colIndex, c): projections) (colIndex + 1) qr

        mkProj [] projections _        q' =
          return (projections, q')

    (ps, qp) <- mkProj projs [] 1 q
    qr <- proj ([colP descr, colP pos] ++ (reverse ps)) qp
    return qr

-- The VectorAlgebra instance for Pathfinder algebra

instance VectorAlgebra PFAlgebra where

  vecBinExpr expr (DVec q1 _) (DVec q2 cols2) = do
    q <- applyBinExpr (length cols2) expr q1 q2
    return $ DVec q [1]

  vecZip (DVec q1 cols1) (DVec q2 cols2) = do
    (r, cols') <- doZip (q1, cols1) (q2, cols2)
    return $ DVec r cols'

  vecLit tys [] = do
    qr <- emptyTable ((descr, natT):(pos, natT):[(itemi i, algTy t) | (i, t) <- zip [1..] tys])
    return $ DVec qr [1..length tys]

  vecLit tys vs = do
    qr <- flip litTable' ((descr, natT):(pos, natT):[(itemi i, algTy t) | (i, t) <- zip [1..] tys])
                                 $ map (map algVal) vs
    return $ DVec qr [1..length tys]

  vecPropRename (RVec q1) (DVec q2 cols) = do
    q <- tagM "propRename"
         $ projM (keepItems cols [(descr, posnew), colP pos])
         $ eqJoin posold descr q1 q2
    return $ DVec q cols

  vecPropFilter (RVec q1) (DVec q2 cols) = do
    q <- rownumM pos' [posnew, pos] Nothing $ eqJoin posold descr q1 q2
    qr1 <- flip DVec cols <$> proj (keepItems cols [(descr, posnew), (pos, pos')]) q
    qr2 <- RVec <$> proj [(posold, pos), (posnew, pos')] q
    return $ (qr1, qr2)

  -- For Pathfinder algebra, the filter and reorder cases are the same, since
  -- numbering to generate positions is done with a rownum and involves sorting.
  vecPropReorder (PVec q1) e2 = do
    (p, (RVec r)) <- vecPropFilter (RVec q1) e2
    return (p, PVec r)

  vecRestrict (DVec q1 cols) (DVec qm _) = do
    q <- rownumM pos'' [pos] Nothing
           $ selectM resCol
           $ eqJoinM pos pos' (return q1)
           $ proj [(pos', pos), (resCol, item)] qm
    qr <- tagM "restrictVec/1" $ proj (keepItems cols [(pos, pos''), colP descr]) q
    qp <- proj [(posold, pos), (posnew, pos'')] q
    return $ (DVec qr cols, RVec qp)

  vecCombine (DVec qb _) (DVec q1 cols) (DVec q2 _) = do
    d1 <- projM [colP pos', colP pos]
            $ rownumM pos' [pos] Nothing
            $ select item qb
    d2 <- projM [colP pos', colP pos]
          $ rownumM pos' [pos] Nothing
          $ selectM resCol
          $ notC resCol item qb
    q <- eqJoinM pos' posold (return d1) (proj (keepItems cols [(posold, pos), colP descr]) q1)
         `unionM`
         eqJoinM pos' posold (return d2) (proj (keepItems cols [(posold, pos), colP descr]) q2)
    qr <- proj (keepItems cols [colP descr, colP pos]) q
    qp1 <- proj [(posnew, pos), (posold, pos')] d1
    qp2 <- proj [(posnew, pos), (posold, pos')] d2
    return $ (DVec qr cols, RVec qp1, RVec qp2)

  vecSegment (DVec q cols) = do
    flip DVec cols <$> proj (keepItems cols [(descr, pos), colP pos]) q

  vecUnsegment (DVec q cols) = do
    qr <- attachM descr natT (nat 1) $ proj (keepItems cols [colP pos]) q
    return $ DVec qr cols

  vecDistPrim (DVec q1 cols) (DVec q2 _) = do
    qr <- crossM 
            (proj [(itemi i, itemi i) | i <- cols] q1) 
            (proj [colP descr, colP pos] q2)
    r <- proj [(posnew, pos), (posold, descr)] q2
    return (DVec qr cols, PVec r)

  vecDistDesc (DVec q1 cols) (DVec q2 _) = do
    q <- projM (keepItems cols [(descr, pos), (pos, pos''), (posold, posold)])
           $ rownumM pos'' [pos, pos'] Nothing
           $ crossM
               (proj [colP pos] q2)
               (proj (keepItems cols [(pos', pos), (posold, pos)]) q1)
    qr1 <- flip DVec cols <$> proj (keepItems cols [colP descr, colP pos]) q
    qr2 <- PVec <$> proj [(posold, posold), (posnew, pos)] q
    return $ (qr1, qr2)

  vecDistSeg (DVec q1 cols) (DVec q2 _) = do
    q <- eqJoinM pos' descr 
           (proj (keepItems cols [(pos', pos)]) q1) 
           (proj [(descr, descr), (pos, pos)] q2)
    qr1 <- tagM "distLift/1" $ proj (keepItems cols [colP descr, colP pos]) q
    qr2 <- proj [(posold, pos'), (posnew, pos)] q
    return $ (DVec qr1 cols, PVec qr2)

  vecLength (DVec d _) = do
    qr <- attachM descr natT (nat 1)
            $ attachM pos natT (nat 1)
            $ aggrM [(Max item, item)] Nothing
            $ (litTable (int 0) item intT)
              `unionM`
              (aggrM [(Count, item)] Nothing $ proj [colP pos] d)
    return $ DVec qr [1]

  vecLengthS (DVec q1 _) (DVec d _) = do
    qr <- rownumM pos [descr] Nothing
            $ aggrM [(Max item, item)] (Just descr)
            $ (attachM item intT (int 0) $ proj [(descr, pos)] q1)
              `unionM`
              (aggrM [(Count, item)] (Just descr) $ proj [colP descr] d)
    return $ DVec qr [1]

  vecReverse (DVec q cols) = do
    q' <- rownum' pos' [(pos, Desc)] Nothing q
    r <- proj (keepItems cols [colP descr, (pos, pos')]) q'
    p <- proj [(posold, pos), (posnew, pos')] q'
    return (DVec r cols, PVec p)

  vecReverseS (DVec q cols) = do
    q' <- rownum' pos' [(descr, Asc), (pos, Desc)] Nothing q
    r <- proj (keepItems cols [colP descr, (pos, pos')]) q'
    p <- proj [(posold, pos), (posnew, pos')] q'
    return (DVec r cols, PVec p)

  vecUnique (DVec q cols) = do
    f <- rownumM posnew [posold] Nothing
           $ aggrM [(Min pos, posold)] (Just resCol)
           $ rank resCol [(itemi i, Asc) | i <- cols] q

    qr <- projM (keepItems cols [colP descr, (pos, posnew)]) $ eqJoin pos posold q f
    return $ DVec qr cols

  vecUniqueS (DVec q cols) = do
    f <- rownumM posnew [posold] Nothing
           $ aggrM [(Min pos, posold)] (Just resCol)
           $ rank resCol ((descr, Asc):[(itemi i, Asc) | i <- cols]) q
    qr <- projM (keepItems cols [colP descr, (pos, posnew)]) 
          $ eqJoin pos posold q f
    return $ DVec qr cols

  vecMin (DVec q _) = do
    qr <- tagM "vecMin" $ attachM descr natT (nat 1)
            $ attachM pos natT (nat 1)
            $ aggr [(Min item, item)] Nothing q
    return $ DVec qr [1]

  vecMax (DVec q _) = do
    qr <- attachM descr natT (nat 1)
            $ attachM pos natT (nat 1)
            $ aggr [(Max item, item)] Nothing q
    return $ DVec qr [1]

  vecMinS (DVec qv _) = do
    qr <- tagM "vecMinLift" $ projM [colP descr,colP pos,colP item]
            $ rownumM pos [descr] Nothing
            $ aggr [(Min item, item)] (Just descr) qv
    return $ DVec qr [1]

  vecMaxS (DVec qv _) = do
    qr <- projM [colP descr,colP pos,colP item]
            $ rownumM pos [descr] Nothing
            $ aggr [(Max item, item)] (Just descr) qv
    return $ DVec qr [1]

  descToRename (DVec q1 _) = RVec <$> proj [(posnew, descr), (posold, pos)] q1

  singletonDescr = do
    q <- attachM pos natT (nat 1) $ litTable (nat 1) descr natT
    return $ DVec q []

  vecAppend (DVec q1 cols) (DVec q2 cols2) = do
    q <- rownumM pos' [descr, ordCol, pos] Nothing
           $ attach ordCol natT (nat 1) q1
             `unionM`
             attach ordCol natT (nat 2) q2
    qv <- tagM "append r" (proj (keepItems cols [(pos, pos'), colP descr]) q)
    qp1 <- tagM "append r1"
           $ projM [(posold, pos), (posnew, pos')]
           $ selectM resCol
           $ operM (RelFun Eq) resCol ordCol tmpCol
           $ attach tmpCol natT (nat 1) q
    qp2 <- tagM "append r2"
           $ projM [(posold, pos), (posnew, pos')]
           $ selectM resCol
           $ operM (RelFun Eq) resCol ordCol tmpCol
           $ attach tmpCol natT (nat 2) q
    return $ (DVec qv cols, RVec qp1, RVec qp2)

  vecSum t (DVec q _) = do
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
         $ aggrM [(Sum item, item)] Nothing
         $ union q' q
    return $ DVec qs [1]
    
  vecAvg (DVec q _) = do
    qa <- attachM descr natT (nat 1)
          $ attachM pos natT (nat 1)
          $ aggr [(Avg item, item)] Nothing q
    return $ DVec qa [1] 
  
  vecAvgS (DVec _qd _) (DVec qv _) = do
    qa <- attachM pos natT (nat 1)
          $ aggr [(Avg item, item)] (Just descr) qv
    return $ DVec qa [1]

  vecSumS (DVec qd _) (DVec qv _) = do
    qe <- attachM item intT (int 0) -- TODO: In general you do not know that it should be an int, it might be double or nat...
          $ differenceM
            (proj [(descr, pos)] qd)
            (proj [colP descr] qv)
    qs <- aggr [(Sum item, item)] (Just descr) qv
    qr <- rownumM pos [descr] Nothing
          $ union qe qs
    -- align the result vector with the original descriptor vector to get
    -- the proper descriptor values (sum removes one list type constructor)
    qa <- projM [(descr, descr'), colP pos, (item, item)]
          $ (eqJoinM pos' descr
             (proj [(descr', descr), (pos', pos)] qd)
             (return qr))
    return $ DVec qa [1]

  vecSelect expr (DVec q cols) = do
    (qe, ce) <- compileExpr1 cols q expr
    qs <- projM (keepItems cols [colP descr, (pos, pos')]) 
          $ rownumM pos' [pos] Nothing
          $ select ce qe
    return $ DVec qs cols

  falsePositions (DVec q1 _) = do
    qr <- projM [colP descr, (pos, pos''), (item, pos')]
          $ rownumM pos'' [pos] Nothing
          $ selectM item
          $ rownumM pos' [pos] (Just descr)
          $ projM [colP pos, colP descr, (item, tmpCol)] $ notC tmpCol item q1
    return $ DVec qr [1]

  vecTableRef n cs ks = do
    table <- dbTable n (renameCols cs) keyItems
    t' <- attachM descr natT (nat 1) $ rownum pos (head keyItems) Nothing table
    cs' <- tagM "table" $ proj (colP descr:colP pos:[(itemi i, itemi i) | i <- [1..length cs]]) t'
    return $ DVec cs' [1..length cs]

    where
      renameCols :: [VL.TypedColumn] -> [Column]
      renameCols xs = [NCol cn [Col i $ algTy t] | ((cn, t), i) <- zip xs [1..]]

      numberedCols = zip cs [1 :: Integer .. ]
      numberedColNames = map (\(c, i) -> (fst c, i)) numberedCols

      keyItems = map (map (\c -> "item" ++ (show $ fromJust $ lookup c numberedColNames))) ks

  vecSort (DVec qs colss) (DVec qe colse) = do
    q <- tagM "sortWith"
         $ eqJoinM pos pos''
           (projM [colP pos, colP pos']
              $ rownum pos' (descr : [itemi i | i <- colss] ++ [pos]) Nothing qs)
           (proj (keepItems colse [colP descr, (pos'', pos)]) qe)
    qv <- proj (keepItems colse [colP descr, (pos, pos')]) q
    qp <- proj [(posold, pos''), (posnew, pos')] q
    return $ (DVec qv colse, PVec qp)

  vecGroupBy (DVec v1 colsg) (DVec v2 colse) = do 
    q' <- rownumM pos' [resCol, pos] Nothing
            $ rowrank resCol ((descr, Asc):[(itemi i, Asc) | i<- colsg]) v1
    d1 <- distinctM 
          $ proj (keepItems colsg [colP descr, (pos, resCol)]) q'
    p <- proj [(posold, pos), (posnew, pos')] q'
    v <- tagM "groupBy ValueVector" 
           $ projM (keepItems colse [colP descr, colP pos])
           $ eqJoinM pos'' pos' (proj [(descr, resCol), (pos, pos'), (pos'', pos)] q')
                                (proj ((pos', pos):[(itemi i, itemi i) | i <- colse]) v2)
    return $ (DVec d1 colsg, DVec v colse, PVec p)

  vecCartProduct (DVec q1 cols1) (DVec q2 cols2) = do
    let itemProj1  = map (colP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zip (map itemi cols2') (map itemi cols2)
        itemProj2  = map (colP . itemi) cols2'
    q <- projM ([(descr, pos), colP pos, colP pos', colP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [pos', pos'] Nothing
           $ crossM
             (proj ([colP descr, (pos', pos)] ++ itemProj1) q1)
             (proj ((pos'', pos) : shiftProj2) q2)
    qv <- proj ([colP  descr, colP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [(posold, pos'), (posnew, pos)] q
    qp2 <- proj [(posold, pos''), (posnew, pos)] q
    return (DVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)

  vecCartProductS (DVec q1 cols1) (DVec q2 cols2) = do
    let itemProj1  = map (colP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zip (map itemi cols2') (map itemi cols2)
        itemProj2  = map (colP . itemi) cols2'
    q <- projM ([(descr, pos), colP pos, colP pos', colP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [descr, descr', pos, pos'] Nothing
           $ eqJoinM descr descr'
             (proj ([colP descr, (pos', pos)] ++ itemProj1) q1)
             (proj ([(descr', descr), (pos'', pos)] ++ shiftProj2) q2)
    qv <- proj ([colP  descr, colP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [(posold, pos'), (posnew, pos)] q
    qp2 <- proj [(posold, pos''), (posnew, pos)] q
    return (DVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)
    
    
  vecEquiJoin leftExpr rightExpr (DVec q1 cols1) (DVec q2 cols2) = do
    let itemProj1  = map (colP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zip (map itemi cols2') (map itemi cols2)
        itemProj2  = map (colP . itemi) cols2'

    (ql, cl) <- compileExpr1 cols1 q1 leftExpr
    (qr, cr) <- compileExpr1 cols2 q2 rightExpr

    q <- projM ([colP descr, colP pos, colP pos', colP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [pos', pos''] Nothing
           $ thetaJoinM [(tmpCol, tmpCol', EqJ)]
             (proj ([colP descr, (pos', pos), (tmpCol, cl)] ++ itemProj1) ql)
             (proj ([(pos'', pos), (tmpCol', cr)] ++ shiftProj2) qr)

    qv <- tagM "eqjoin/1" $ proj ([colP  descr, colP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [(posold, pos'), (posnew, pos)] q
    qp2 <- proj [(posold, pos''), (posnew, pos)] q
    return (DVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)
  
  vecEquiJoinS leftExpr rightExpr (DVec q1 cols1) (DVec q2 cols2) = do
    let itemProj1  = map (colP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zip (map itemi cols2') (map itemi cols2)
        itemProj2  = map (colP . itemi) cols2'

    (ql, cl) <- compileExpr1 cols1 q1 leftExpr
    (qr, cr) <- compileExpr1 cols2 q2 rightExpr

    q <- projM ([colP descr, colP pos, colP pos', colP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [pos', pos''] Nothing
           $ thetaJoinM [(descr, descr', EqJ), (tmpCol, tmpCol', EqJ)]
             (proj ([colP descr, (pos', pos), (tmpCol, cl)] ++ itemProj1) ql)
             (proj ([(descr', descr), (pos'', pos), (tmpCol', cr)] ++ shiftProj2) qr)

    qv <- proj ([colP  descr, colP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [(posold, pos'), (posnew, pos)] q
    qp2 <- proj [(posold, pos''), (posnew, pos)] q
    return (DVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)
  
  selectPos (DVec qe cols) op (DVec qi _) = do
    qx <- crossM
            (proj (keepItems cols [colP descr, (pos', pos)]) qe)
            -- (proj (pf [colP descr, (pos', pos)]) qe)
            (projM [colP item'] $ cast item' item natT qi)
    qn <- case op of
            VL.Lt ->
                projM (keepItems cols [colP descr, (pos, pos'), colP pos'])
                  $ selectM resCol
                  $ oper (RelFun Lt) resCol pos' item' qx
            VL.LtE -> do
                (compNode, compCol) <- runExprComp $ specialComparison qx pos' item' (RelFun Lt)
                projM (keepItems cols [colP descr, (pos, pos'), colP pos'])
                  $ select compCol compNode
            VL.GtE -> do
                (compNode, compCol) <- runExprComp $ specialComparison qx item' pos' (RelFun Lt)
                projM (keepItems cols [colP descr, (pos, pos''), colP pos'])
                  $ rownumM pos'' [pos'] Nothing
                  $ select compCol compNode
            _ ->
                projM (keepItems cols [colP descr, colP pos, colP pos'])
                 $ rownumM pos [descr, pos'] Nothing
                    $ selectM resCol
                        $ oper (algCompOp op) resCol pos' item' qx
    q <- proj (keepItems cols [colP descr, colP pos]) qn
    qp <- proj [(posnew, pos), (posold, pos')] qn
    return $ (DVec q cols, RVec qp)

  selectPosS (DVec qe cols) op (DVec qi _) = do
    qx <- castM pos''' pos' intT
            $ eqJoinM descr pos''
                (rownum pos' [pos] (Just descr) qe)
                (proj [(pos'', pos), (item', item)] qi)
    qs <- case op of
        VL.LtE -> do
                (compNode, compCol) <- runExprComp $ specialComparison qx pos''' item' (RelFun Lt)
                rownumM posnew [descr, pos] Nothing
                  $ projM (keepItems cols [colP descr, (pos, pos'), colP pos'])
                  $ select compCol compNode

        _ -> rownumM posnew [descr, pos] Nothing
              $ selectM resCol
              $ oper (algCompOp op) resCol pos''' item' qx
    q <- proj (keepItems cols [colP descr, (pos, posnew)]) qs
    qp <- proj [(posold, pos), (posnew, posnew)] qs
    return $ (DVec q cols, RVec qp)

  selectPos1 (DVec qe cols) op (VL.N posConst) = do
    qi <- attach pos' ANat (VNat $ fromIntegral posConst) qe
    q' <- case op of
            VL.Lt -> do
              projM (keepItems cols [colP descr, colP pos, (pos'', pos)])
              $ selectM resCol
              $ oper (RelFun Lt) resCol pos pos' qi
            VL.LtE -> do
              projM (keepItems cols [colP descr, colP pos, (pos'', pos)])
                $ selectM resCol
                $ (oper (RelFun Eq) resCol pos pos') qi
                  `unionM`
                  (oper (RelFun Lt) resCol pos pos') qi
            _ -> do
              projM (keepItems cols [colP descr, colP pos, colP pos''])
                $ rownumM pos'' [pos] Nothing
                $ selectM resCol
                $ oper (algCompOp op) resCol pos pos' qi
    qr <- proj (keepItems cols [colP descr, (pos, pos'')]) q'
    qp <- proj [(posold, pos), (posnew, pos'')] q'
    return $ (DVec qr cols, RVec qp)

  selectPos1S (DVec qe cols) op (VL.N posConst) = do
    qi <- rownumM pos'' [pos] (Just descr)
            $ attach pos' ANat (VNat $ fromIntegral posConst) qe
    q' <- case op of
            VL.Lt -> do
              projM (keepItems cols [colP descr, colP pos, (pos', pos)])
                $ selectM resCol
                $ oper (RelFun Gt) resCol pos'' pos' qi
            VL.LtE -> do
              projM (keepItems cols [colP descr, colP pos, (pos', pos)])
                $ selectM resCol
                $ (oper (RelFun Eq) resCol pos'' pos') qi
                  `unionM`
                  (oper (RelFun Lt) resCol pos'' pos') qi
            _ -> do
              projM (keepItems cols [colP descr, colP pos, colP pos'])
                $ rownumM pos''' [descr, pos] Nothing
                $ selectM resCol
                $ oper (algCompOp op) resCol pos'' pos' qi
    qr <- proj (keepItems cols [colP descr, (pos, pos''')]) q'
    qp <- proj [(posold, pos), (posnew, pos')] q'
    return $ (DVec qr cols, RVec qp)

  projectRename posnewProj posoldProj (DVec q _) = do
    qn <- rownum pos'' [descr, pos] Nothing q
    qr <- case (posnewProj, posoldProj) of
            (VL.STNumber, VL.STNumber) -> proj [(posnew, pos''), (posold, pos'')] qn
            (VL.STNumber, p)           -> proj [(posnew, pos''), transProj posold p] qn
            (p, VL.STNumber)           -> proj [transProj posnew p, (posold, pos'')] qn
            (p1, p2)                   -> proj [transProj posnew p1, transProj posold p2] qn

    return $ RVec qr

  vecProject projs (DVec q _) = do
    qr <- doProject projs q
    return $ DVec qr [1 .. (length projs)]
    
  vecZipS (DVec q1 cols1) (DVec q2 cols2) = do
    q1' <- rownum pos'' [pos] (Just descr) q1
    q2' <- rownum pos''' [pos] (Just descr) q2
    let offset      = length cols1
        cols2'      = map (+ offset) cols2
        allCols     = cols1 ++ cols2'
        allColsProj = map (colP . itemi) allCols
        shiftProj   = zip (map itemi cols2') (map itemi cols2)
    qz <- rownumM posnew [descr, pos''] Nothing
          $ projM ([colP pos', colP pos, colP descr] ++ allColsProj)
          $ thetaJoinM [(descr, descr', EqJ), (pos'', pos''', EqJ)]
              (return q1')
              (proj ([(descr', descr), (pos', pos), colP pos'''] ++ shiftProj) q2')

    r1 <- proj [(posold, pos''), colP posnew] qz
    r2 <- proj [(posold, pos'''), colP posnew] qz
    qr <- proj ([colP descr, (pos, posnew)] ++ allColsProj) qz
    return (DVec qr allCols, RVec r1, RVec r2)
  
  vecAggr = undefined
  {-
  vecAggr groupCols aggrFuns (DVec q _) = do
    let mPartAttrs = case groupCols of
                         []         -> Nothing
                         [groupCol] -> Just $ itemi groupCol
                         _          -> undefined
  
    let pfAggrFuns = zipWith (\a i -> (a, itemi i)) (map aggrFun aggrFuns) [1..]
                 
    qa <- rownum
          $ aggr pfAggrFuns mPartAttrs q
  -}
                 
      
  
  vecNumber (DVec q cols) = do
    let nrIndex = length cols + 1
        nrItem = itemi nrIndex
    qr <- cast nrItem pos natT q
    return $ DVec qr (cols ++ [nrIndex])
  
  -- The Pathfinder implementation of lifted number does not come for free: To
  -- generate the absolute numbers for every sublist (i.e. descriptor
  -- partition), we have to use a partitioned rownumber.
  vecNumberS (DVec q cols) = do
    let nrIndex = length cols + 1
        nrItem = itemi nrIndex
    qr <- rownum nrItem [pos] (Just descr) q
    return $ DVec qr (cols ++ [nrIndex])
  
  vecSemiJoin leftExpr rightExpr (DVec q1 cols1) (DVec q2 cols2) = do
    (ql, cl) <- compileExpr1 cols1 q1 leftExpr
    (qr, cr) <- compileExpr1 cols2 q2 rightExpr
    q <- rownumM pos [posold] Nothing
         $ projM (keepItems cols1 [colP descr, (posold, pos)])
         $ semiJoinM [(tmpCol, tmpCol', EqJ)]
             (proj (keepItems cols1 [colP descr, colP pos, (tmpCol, cl)]) ql)
             (proj [(tmpCol', cr)] qr)
    qj <- tagM "semijoin/1" $ proj (keepItems cols1 [colP descr, colP pos]) q
    r  <- proj [colP posold, (posold, posnew)] q
    return $ (DVec qj cols1, RVec r)
  
  vecSemiJoinS leftExpr rightExpr (DVec q1 cols1) (DVec q2 cols2) = do
    (ql, cl) <- compileExpr1 cols1 q1 leftExpr
    (qr, cr) <- compileExpr1 cols2 q2 rightExpr
    q <- rownumM pos [descr, posold] Nothing
         $ projM (keepItems cols1 [colP descr, (posold, pos)])
         $ semiJoinM [(descr, descr', EqJ), (tmpCol, tmpCol', EqJ)]
             (proj (keepItems cols1 [colP descr, colP pos, (tmpCol, cl)]) ql)
             (proj [(descr', descr), (tmpCol', cr)] qr)
    qj <- tagM "semijoinLift/1" $ proj (keepItems cols1 [colP descr, colP pos]) q
    r  <- proj [colP posold, (posold, posnew)] q
    return $ (DVec qj cols1, RVec r)
  
  vecAntiJoin leftExpr rightExpr (DVec q1 cols1) (DVec q2 cols2) = do
    (ql, cl) <- compileExpr1 cols1 q1 leftExpr
    (qr, cr) <- compileExpr1 cols2 q2 rightExpr
    q <- rownumM pos [posold] Nothing
         $ projM (keepItems cols1 [colP descr, (posold, pos)])
         $ antiJoinM [(tmpCol, tmpCol', EqJ)]
             (proj (keepItems cols1 [colP descr, colP pos, (tmpCol, cl)]) ql)
             (proj [(tmpCol', cr)] qr)
    qj <- tagM "antijoin/1" $ proj (keepItems cols1 [colP descr, colP pos]) q
    r  <- proj [colP posold, (posold, posnew)] q
    return $ (DVec qj cols1, RVec r)
  
  -- FIXME re-check semantics!
  vecAntiJoinS leftExpr rightExpr (DVec q1 cols1) (DVec q2 cols2) = do
    (ql, cl) <- compileExpr1 cols1 q1 leftExpr
    (qr, cr) <- compileExpr1 cols2 q2 rightExpr
    q <- rownumM pos [descr, posold] Nothing
         $ projM (keepItems cols1 [colP descr, (posold, pos)])
         $ antiJoinM [(descr, descr', EqJ), (tmpCol, tmpCol', EqJ)]
             (proj (keepItems cols1 [colP descr, colP pos, (tmpCol, cl)]) ql)
             (proj [(descr', descr), (tmpCol', cr)] qr)
    qj <- tagM "antijoinLift/1" $ proj (keepItems cols1 [colP descr, colP pos]) q
    r  <- proj [colP posold, (posold, posnew)] q
    return $ (DVec qj cols1, RVec r)
