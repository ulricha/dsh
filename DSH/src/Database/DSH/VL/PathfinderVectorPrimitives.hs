{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VL.PathfinderVectorPrimitives() where
       
import           Debug.Trace
import           Text.Printf

import           Data.Maybe

import           Control.Applicative                         hiding (Const)

import           Control.Monad.State

import qualified Database.Algebra.VL.Data                    as VL
import           Database.DSH.Impossible
import           Database.DSH.VL.Data.DBVector
import           Database.DSH.VL.VectorPrimitives

import           Database.Algebra.Dag.Builder
import           Database.Algebra.Pathfinder

-- Some general helpers

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

itemi :: Int -> AttrName
itemi i = "item" ++ show i

itemi' :: Int -> AttrName
itemi' i = "item9999910" ++ show i

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

-- Compilation of VL expressions (Expr1, Expr2)

type ExprComp r a = StateT Int (GraphM r PFAlgebra) a

freshCol :: ExprComp r AttrName
freshCol = do
  i <- get
  put $ i + 1
  return $ itemi' i

runExprComp :: ExprComp r a -> GraphM r PFAlgebra a
runExprComp m = evalStateT m 1

specialComparison :: AlgNode -> AttrName -> AttrName -> String -> ExprComp r (AlgNode, AttrName)
specialComparison n leftArg rightArg op = do
  opCol    <- freshCol
  opNode   <- lift $ oper op opCol leftArg rightArg n
  eqCol    <- freshCol
  eqNode   <- lift $ oper "==" eqCol leftArg rightArg opNode
  orCol    <- freshCol
  andNode  <- lift $ oper "||" orCol opCol eqCol eqNode
  return (andNode, orCol)

compileExpr1' :: [DBCol] -> AlgNode -> VL.Expr1 -> ExprComp r (AlgNode, AttrName)
compileExpr1' cols n (VL.App1 (VL.COp VL.LtE) e1 e2) = do
  (n1, c1) <- compileExpr1' cols n e1
  (n2, c2) <- compileExpr1' cols n1 e2
  specialComparison n2 c1 c2 "<"
compileExpr1' cols n (VL.App1 (VL.COp VL.GtE) e1 e2) = do
  (n1, c1) <- compileExpr1' cols n e1
  (n2, c2) <- compileExpr1' cols n1 e2
  specialComparison n2 c1 c2 ">"

compileExpr1' cols n (VL.App1 op e1 e2)   = do
  col      <- freshCol
  (n1, c1) <- compileExpr1' cols n e1
  (n2, c2) <- compileExpr1' cols n1 e2
  nr <- lift $ oper (show op) col c1 c2 n2
  return (nr, col)
compileExpr1' cols n (VL.Column1 dbcol)   = do
  col <- freshCol
  nr <- trace (printf "fresh %s" col) $ lift $ proj (keepItems cols [colP descr, colP pos, (col, itemi dbcol)]) n
  return (nr, col)
compileExpr1' cols n (VL.Constant1 constVal) = do
  col <- freshCol
  let ty  = algConstType constVal
      val = algVal constVal
  nr <- lift $ attach col ty val n
  return (nr, col)

compileExpr1 :: [DBCol] -> AlgNode -> VL.Expr1 -> GraphM r PFAlgebra (AlgNode, AttrName)
compileExpr1 cols n e = runExprComp (compileExpr1' cols n e)

compileExpr2' :: AlgNode -> VL.Expr2 -> ExprComp r (AlgNode, AttrName)
compileExpr2' n (VL.App2 (VL.COp VL.LtE) e1 e2) = do
  (n1, c1) <- compileExpr2' n e1
  (n2, c2) <- compileExpr2' n1 e2
  specialComparison n2 c1 c2 "<"

compileExpr2' n (VL.App2 (VL.COp VL.GtE) e1 e2) = do
  (n1, c1) <- compileExpr2' n e1
  (n2, c2) <- compileExpr2' n1 e2
  specialComparison n2 c1 c2 ">"

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

-- Common building blocks

doNot :: AlgNode -> GraphM r PFAlgebra AlgNode
doNot q = projM [colP pos, colP descr, (item, tmpCol)] $ notC tmpCol item q

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
               -- shift the column names on the rigth to avoid name collisions
               $ proj ((pos', pos) : colShift) q2
  (qr, cr) <- compileExpr2 qCombined e
  proj [colP descr, colP pos, (item, cr)] qr

-- The VectorAlgebra instance for Pathfinder algebra

instance VectorAlgebra PFAlgebra where

  compExpr1 expr (DBV q _) = do
    (qr, cr) <- compileExpr1 [1] q expr
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

  notPrim (DBP q _) = flip DBP [1] <$> doNot q

  notVec (DBV d _) = flip DBV [1] <$> doNot d

  distPrim (DBP q1 cols) (DBV q2 _) = do
    qr <- crossM 
            (proj [(itemi i, itemi i) | i <- cols] q1) 
            (proj [colP descr, colP pos] q2)
    r <- proj [(posnew, pos), (posold, descr)] q2
    return (DBV qr cols, PropVector r)

  distDesc (DBV q1 cols) (DBV q2 _) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols ]
    q <- projM (pf [(descr, pos), (pos, pos''), (posold, posold)])
           $ rownumM pos'' [pos, pos'] Nothing
           $ crossM
               (proj [colP pos] q2)
               (proj (pf [(pos', pos), (posold, pos)]) q1)
    qr1 <- flip DBV cols <$> proj (pf [colP descr, colP pos]) q
    qr2 <- PropVector <$> proj [(posold, posold), (posnew, pos)] q
    return $ (qr1, qr2)

  distLift (DBV q1 cols) (DBV q2 _) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    q <- eqJoinM pos' descr 
           (proj (pf [(pos', pos)]) q1) 
           (proj [(descr, descr), (pos, pos)] q2)
    qr1 <- flip DBV cols <$> proj (pf [colP descr, colP pos]) q
    qr2 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] q
    return $ (qr1, qr2)

  lengthA (DBV d _) = do
    qr <- attachM descr natT (nat 1)
            $ attachM pos natT (nat 1)
            $ aggrM [(Max, item, Just item)] Nothing
            $ (litTable (int 0) item intT)
              `unionM`
              (aggrM [(Count, item, Nothing)] Nothing $ proj [colP pos] d)
    return $ DBP qr [1]

  lengthSeg (DBV q1 _) (DBV d _) = do
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

  descToRename (DBV q1 _) = RenameVector <$> proj [(posnew, descr), (posold, pos)] q1

  singletonDescr = do
    q <- attachM pos natT (nat 1) $ litTable (nat 1) descr natT
    return $ DBV q []

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
    
  vecAvg (DBV q _) = do
    qa <- attachM descr natT (nat 1)
          $ attachM pos natT (nat 1)
          $ aggr [(Avg, item, Just item)] Nothing q
    return $ DBP qa [1] 
  
  vecAvgLift (DBV _qd _) (DBV qv _) = do
    qa <- attachM pos natT (nat 1)
          $ aggr [(Avg, item, Just item)] (Just descr) qv
    return $ DBV qa [1]

  vecSumLift (DBV qd _) (DBV qv _) = do
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
    (qe, ce) <- compileExpr1 cols q expr
    qr <- projM (pf [colP descr, colP pos])
          $ eqJoinM pos pos'
              (return q)
              (proj [(pos', pos), colP ce] qe)
    return $ DBV qr cols

  falsePositions (DBV q1 _) = do
    qr <- projM [colP descr, (pos, pos''), (item, pos')]
          $ rownumM pos'' [pos] Nothing
          $ selectM item
          $ rownumM pos' [pos] (Just descr)
          $ doNot q1
    return $ DBV qr [1]

  tableRef n cs ks = do
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

  sortWith (DBV qs colss) (DBV qe colse) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- colse]
    q <- tagM "sortWith"
         $ eqJoinM pos pos''
           (projM [colP pos, colP pos']
              $ rownum pos' (descr : [itemi i | i <- colss] ++ [pos]) Nothing qs)
           (proj (pf [colP descr, (pos'', pos)]) qe)
    qv <- proj (pf [colP descr, (pos, pos')]) q
    qp <- proj [(posold, pos''), (posnew, pos')] q
    return $ (DBV qv colse, PropVector qp)

  groupByKey (DBV v1 colsg) (DBV v2 colse) = do 
    q' <- rownumM pos' [resCol, pos] Nothing
            $ rowrank resCol ((descr, Asc):[(itemi i, Asc) | i<- colsg]) v1
    d1 <- distinctM 
          $ proj ([colP descr, (pos, resCol)] ++ [ (itemi i, itemi i) | i <- colsg ]) q'
    p <- proj [(posold, pos), (posnew, pos')] q'
    v <- tagM "groupBy ValueVector" $ projM [colP descr, colP pos, (item, item)]
           $ eqJoinM pos'' pos' (proj [(descr, resCol), (pos, pos'), (pos'', pos)] q')
                                (proj ((pos', pos):[(itemi i, itemi i) | i <- colse]) v2)
    return $ (DBV d1 colsg, DBV v colse, PropVector p)

  cartProduct (DBV q1 cols1) (DBV q2 cols2) = trace "foo" $ do
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
    return (DBV qv (cols1 ++ cols2'), PropVector qp1, PropVector qp2)
    
  equiJoin leftExpr rightExpr (DBV q1 cols1) (DBV q2 cols2) = do
    let itemProj1  = map (colP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zip (map itemi cols2') (map itemi cols2)
        itemProj2  = map (colP . itemi) cols2'
    (ql, cl) <- compileExpr1 cols1 q1 leftExpr
    (qr, cr) <- compileExpr1 cols2 q2 rightExpr
    q <- projM ([(descr, pos), colP pos, colP pos', colP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [pos', pos''] Nothing
           $ thetaJoinM [(tmpCol, tmpCol', "==")]
             (proj ([colP descr, (pos', pos), (tmpCol, cl)] ++ itemProj1) ql)
             (proj ([(pos'', pos), (tmpCol', cr)] ++ shiftProj2) qr)
    qv <- proj ([colP  descr, colP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [(posold, pos'), (posnew, pos)] q
    qp2 <- proj [(posold, pos''), (posnew, pos)] q
    return (DBV qv (cols1 ++ cols2'), PropVector qp1, PropVector qp2)
  
  equiJoinL leftExpr rightExpr (DBV q1 cols1) (DBV q2 cols2) = undefined
  
  selectPos (DBV qe cols) op (DBP qi _) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    qx <- crossM
            (proj (pf [colP descr, (pos', pos)]) qe)
            -- (proj (pf [colP descr, (pos', pos)]) qe)
            (projM [colP item'] $ cast item item' natT qi)
    qn <- case op of
            VL.Lt ->
                projM (pf [colP descr, (pos, pos'), colP pos'])
                  $ selectM resCol
                  $ oper (show op) resCol pos' item' qx
            VL.LtE -> do
                (compNode, compCol) <- runExprComp $ specialComparison qx pos' item' "<"
                projM (pf [colP descr, (pos, pos'), colP pos'])
                  $ select compCol compNode
            VL.GtE -> do
                (compNode, compCol) <- runExprComp $ specialComparison qx item' pos' "<"
                projM (pf [colP descr, (pos, pos''), colP pos'])
                  $ rownumM pos'' [pos'] Nothing
                  $ select compCol compNode
            _ ->
                projM (pf [colP descr, colP pos, colP pos'])
                 $ rownumM pos [descr, pos'] Nothing
                    $ selectM resCol
                        $ oper (show op) resCol pos' item' qx
    q <- proj (pf [colP descr, colP pos]) qn
    qp <- proj [(posnew, pos), (posold, pos')] qn
    return $ (DBV q cols, RenameVector qp)

  selectPosLift (DBV qe cols) op (DBV qi _) = do
    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
    qx <- castM pos' pos''' intT
            $ eqJoinM descr pos''
                (rownum pos' [pos] (Just descr) qe)
                (proj [(pos'', pos), (item', item)] qi)
    qs <- case op of
        VL.LtE -> do
                (compNode, compCol) <- runExprComp $ specialComparison qx pos''' item' "<"
                rownumM posnew [descr, pos] Nothing
                  $ projM (pf [colP descr, (pos, pos'), colP pos'])
                  $ select compCol compNode

        _ -> rownumM posnew [descr, pos] Nothing
              $ selectM resCol
              $ oper (show op) resCol pos''' item' qx
    q <- proj (pf [colP descr, (pos, posnew)]) qs
    qp <- proj [(posold, pos), (posnew, posnew)] qs
    return $ (DBV q cols, RenameVector qp)

  selectPos1 (DBV qe cols) op (VL.N posConst) = do
    let pf = \x -> x ++ [colP $ itemi i | i <- cols]
    qi <- attach pos' ANat (VNat $ fromIntegral posConst) qe
    q' <- case op of
            VL.Lt -> do
              projM (pf [colP descr, colP pos, (pos'', pos)])
              $ selectM resCol
              $ oper (show op) resCol pos pos' qi
            VL.LtE -> do
              projM (pf [colP descr, colP pos, (pos'', pos)])
                $ selectM resCol
                $ (oper (show VL.Eq) resCol pos pos') qi
                  `unionM`
                  (oper (show VL.Lt) resCol pos pos') qi
            _ -> do
              projM (pf [colP descr, colP pos, colP pos''])
                $ rownumM pos'' [pos] Nothing
                $ selectM resCol
                $ oper (show op) resCol pos pos' qi
    qr <- proj (pf [colP descr, (pos, pos'')]) q'
    qp <- proj [(posold, pos), (posnew, pos'')] q'
    return $ (DBV qr cols, RenameVector qp)

  selectPos1Lift (DBV qe cols) op (VL.N posConst) = do
    let pf = \x -> x ++ [colP $ itemi i | i <- cols]
    qi <- rownumM pos'' [pos] (Just descr)
            $ attach pos' ANat (VNat $ fromIntegral posConst) qe
    q' <- case op of
            VL.Lt -> do
              projM (pf [colP descr, colP pos, (pos', pos)])
                $ selectM resCol
                $ oper (show op) resCol pos'' pos' qi
            VL.LtE -> do
              projM (pf [colP descr, colP pos, (pos', pos)])
                $ selectM resCol
                $ (oper (show VL.Eq) resCol pos'' pos') qi
                  `unionM`
                  (oper (show VL.Lt) resCol pos'' pos') qi
            _ -> do
              projM (pf [colP descr, colP pos, colP pos'])
                $ rownumM pos''' [descr, pos] Nothing
                $ selectM resCol
                $ oper (show op) resCol pos'' pos' qi
    qr <- proj (pf [colP descr, (pos, pos''')]) q'
    qp <- proj [(posold, pos), (posnew, pos')] q'
    return $ (DBV qr cols, RenameVector qp)

  projectRename posnewProj posoldProj (DBV q _) = do
    qn <- rownum pos'' [descr, pos] Nothing q
    qr <- case (posnewProj, posoldProj) of
            (VL.STNumber, VL.STNumber) -> proj [(posnew, pos''), (posold, pos'')] qn
            (VL.STNumber, p)           -> proj [(posnew, pos''), transProj posold p] qn
            (p, VL.STNumber)           -> proj [transProj posnew p, (posold, pos'')] qn
            (p1, p2)                   -> proj [transProj posnew p1, transProj posold p2] qn

    return $ RenameVector qr

  projectPayload valProjs (DBV q _) = do

    let createPayloadProj :: [VL.PayloadProj]
                          -> [(AttrName, AttrName)]
                          -> Int
                          -> AlgNode
                          -> GraphM r PFAlgebra ([(AttrName, AttrName)], AlgNode)
        createPayloadProj ((VL.PLConst c) : vps) projections colIndex q' = do
          qa <- attach (itemi' colIndex) (algConstType c) (algVal c) q'
          createPayloadProj vps ((itemi colIndex, itemi' colIndex) : projections) (colIndex + 1) qa

        createPayloadProj ((VL.PLCol col) : vps) projections colIndex q' =
          createPayloadProj vps ((itemi colIndex, itemi col) : projections) (colIndex + 1) q'

        createPayloadProj []                     projections _        q' =
          return (projections, q')

    (ps, qp) <- createPayloadProj valProjs [] 1 q
    qr <- proj ([colP descr, colP pos] ++ ps) qp
    return $ DBV qr [1 .. (length valProjs)]

  projectAdmin descrProj posProj (DBV q cols) = do
    let pf = \x -> x ++ [colP $ itemi i | i <- cols]
    (pd, qd) <- case descrProj of
                 VL.DescrConst (VL.N c) -> do
                   qa <- attach descr ANat (VNat $ fromIntegral c) q
                   return ((descr, descr), qa)
                 VL.DescrIdentity       -> return ((descr, descr), q)
                 VL.DescrPosCol         -> return ((descr, pos), q)

    qp <- case posProj of
            VL.PosNumber         -> do
              -- FIXME we might want to consider the case that the descriptor has just been overwritten
              -- what to generate numbers from then?
              qn <- rownum pos''' [descr, pos] Nothing qd
              return qn
            VL.PosConst (VL.N c) -> do
              qa <- attach pos ANat (VNat $ fromIntegral c) qd
              return qa
            VL.PosIdentity       -> return qd

    qr <- proj (pf [pd, (pos, pos''')]) qp
    return $ DBV qr cols

  zipL (DBV q1 cols1) (DBV q2 cols2) = do
    q1' <- rownum pos'' [pos] (Just descr) q1
    q2' <- rownum pos''' [pos] (Just descr) q2
    let offset      = length cols1
        cols2'      = map (+ offset) cols2
        allCols     = cols1 ++ cols2'
        allColsProj = map (colP . itemi) allCols
        shiftProj   = zip (map itemi cols2') (map itemi cols2)
    qz <- rownumM posnew [descr, pos''] Nothing
          $ projM ([colP pos', colP pos, colP descr] ++ allColsProj)
          $ thetaJoinM [(descr, descr', "=="), (pos'', pos''', "==")]
              (return q1')
              (proj ([(descr', descr), (pos', pos), colP pos'''] ++ shiftProj) q2')

    r1 <- proj [(posold, pos''), colP posnew] qz
    r2 <- proj [(posold, pos'''), colP posnew] qz
    qr <- proj ([colP descr, (pos, posnew)] ++ allColsProj) qz
    return (DBV qr allCols, RenameVector r1, RenameVector r2)
  
  vecAggr _ _ _ = undefined
