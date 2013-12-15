{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VL.PathfinderVectorPrimitives() where

import           GHC.Exts
       
import           Debug.Trace

import           Data.Maybe

import           Control.Applicative                         hiding (Const)

import qualified Database.Algebra.VL.Data                    as VL
import           Database.DSH.Impossible
import           Database.DSH.VL.Data.DBVector
import           Database.DSH.VL.VectorPrimitives

import           Database.Algebra.Dag.Builder
import           Database.Algebra.Pathfinder
import           Database.Algebra.Pathfinder.Data.Algebra

-- Some general helpers

-- | Results are stored in column:
pos, item', item, descr, descr', descr'', pos', pos'', pos''', posold, posnew, ordCol, resCol, tmpCol, tmpCol' , absPos :: AttrName
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
absPos    = "abspos"

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

cP :: AttrName -> Proj
cP a = (a, ColE a)

eP :: AttrName -> Expr -> Proj
eP = (,)

mP :: AttrName -> AttrName -> Proj
mP n o = (n, ColE o)

projAddCols :: [DBCol] -> [Proj] -> AlgNode -> GraphM r PFAlgebra AlgNode
projAddCols cols projs q = proj ([cP descr, cP pos] ++ map (cP . itemi) cols ++ projs) q

projAddColsM :: [DBCol] -> [Proj] -> GraphM r PFAlgebra AlgNode -> GraphM r PFAlgebra AlgNode
projAddColsM cols projs mq = do
  q <- mq
  projAddCols cols projs q

projIdentity :: [DBCol] -> AlgNode -> GraphM r PFAlgebra AlgNode
projIdentity cols q = projAddCols cols [cP descr, cP pos] q

transProj :: AttrName -> VL.ISTransProj -> Proj
transProj target VL.STPosCol   = mP target pos
transProj target VL.STDescrCol = mP target descr
transProj _      VL.STNumber   = $impossible

itemProj :: [DBCol] -> [Proj] -> [Proj]
itemProj cols projs = projs ++ [ cP $ itemi i | i <- cols ]

binOp :: VL.VecOp -> BinFun
binOp (VL.NOp VL.Add)  = Plus
binOp (VL.NOp VL.Sub)  = Minus
binOp (VL.NOp VL.Div)  = Times
binOp (VL.NOp VL.Mul)  = Div
binOp (VL.NOp VL.Mod)  = Modulo
binOp (VL.COp VL.Eq)   = Eq
binOp (VL.COp VL.Gt)   = Gt
binOp (VL.COp VL.GtE)  = GtE
binOp (VL.COp VL.Lt)   = Lt
binOp (VL.COp VL.LtE)  = LtE
binOp (VL.BOp VL.Conj) = And
binOp (VL.BOp VL.Disj) = Or
binOp VL.Like          = Like

unOp :: VL.VecUnOp -> UnFun
unOp VL.Not                    = Not
unOp (VL.CastOp VL.CastDouble) = Cast doubleT

expr1 :: VL.Expr1 -> Expr
expr1 (VL.BinApp1 op e1 e2) = BinAppE (binOp op) (expr1 e1) (expr1 e2)
expr1 (VL.UnApp1 op e)      = UnAppE (unOp op) (expr1 e)
expr1 (VL.Column1 c)        = ColE $ itemi c
expr1 (VL.Constant1 v)      = ConstE $ algVal v

-- | Vl Expr2 considers two input vectors and may reference columns from the
-- left and right side. Columns from the left map directly to item columns. For
-- right input columns, temporary column names are used.
expr2 :: VL.Expr2 -> Expr
expr2 (VL.BinApp2 op e1 e2)      = BinAppE (binOp op) (expr2 e1) (expr2 e2)
expr2 (VL.UnApp2 op e)           = UnAppE (unOp op) (expr2 e)
expr2 (VL.Column2Left (VL.L c))  = ColE $ itemi c
expr2 (VL.Column2Right (VL.R c)) = ColE $ itemi' c
expr2 (VL.Constant2 v)           = ConstE $ algVal v

aggrFun :: VL.AggrFun -> AggrType
aggrFun (VL.AggrSum c) = Sum $ itemi c
aggrFun (VL.AggrMin c) = Min $ itemi c
aggrFun (VL.AggrMax c) = Max $ itemi c
aggrFun (VL.AggrAvg c) = Avg $ itemi c
aggrFun VL.AggrCount   = Count

-- Common building blocks

doZip :: (AlgNode, [DBCol]) -> (AlgNode, [DBCol]) -> GraphM r PFAlgebra (AlgNode, [DBCol])
doZip (q1, cols1) (q2, cols2) = do
  let offset = length cols1
  let cols' = cols1 ++ map (+offset) cols2
  r <- projM (cP descr : cP pos : map (cP . itemi) cols')
         $ eqJoinM pos pos'
           (return q1)
           (proj ((mP pos' pos):[ mP (itemi $ i + offset) (itemi i) | i <- cols2 ]) q2)
  return (r, cols')

-- The VectorAlgebra instance for Pathfinder algebra

instance VectorAlgebra PFAlgebra where

  vecBinExpr expr (DVec q1 _) (DVec q2 cols2) = do
    let colShift = [ mP (itemi' i) (itemi i) | i <- cols2 ]
    q <- projM [cP descr, cP pos, eP item (expr2 expr)]
         $ eqJoinM pos pos' 
             (return q1)
             -- shift the column names on the right to avoid name collisions
             (proj ((mP pos' pos) : colShift) q2)

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
         $ projM (itemProj cols [mP descr posnew, cP pos])
         $ eqJoin posold descr q1 q2
    return $ DVec q cols

  vecPropFilter (RVec q1) (DVec q2 cols) = do
    q <- rownumM pos' [posnew, pos] Nothing $ eqJoin posold descr q1 q2
    qr1 <- flip DVec cols <$> proj (itemProj cols [mP descr posnew, mP pos pos']) q
    qr2 <- RVec <$> proj [mP posold pos, mP posnew pos'] q
    return $ (qr1, qr2)

  -- For Pathfinder algebra, the filter and reorder cases are the same, since
  -- numbering to generate positions is done with a rownum and involves sorting.
  vecPropReorder (PVec q1) e2 = do
    (p, (RVec r)) <- vecPropFilter (RVec q1) e2
    return (p, PVec r)

  vecRestrict (DVec q1 cols) (DVec qm _) = do
    q <- rownumM pos'' [pos] Nothing
           $ selectM (ColE resCol)
           $ eqJoinM pos pos' (return q1)
           $ proj [mP pos' pos, mP resCol item] qm
    qr <- tagM "restrictVec/1" $ proj (itemProj cols [mP pos pos'', cP descr]) q
    qp <- proj [mP posold pos, mP posnew pos''] q
    return $ (DVec qr cols, RVec qp)

  vecCombine (DVec qb _) (DVec q1 cols) (DVec q2 _) = do
    d1 <- projM [cP pos', cP pos]
            $ rownumM pos' [pos] Nothing
            $ select (ColE item) qb
    d2 <- projM [cP pos', cP pos]
          $ rownumM pos' [pos] Nothing
          $ select (UnAppE Not (ColE item)) qb
    q <- eqJoinM pos' posold 
            (return d1) 
            (proj (itemProj cols [mP posold pos, cP descr]) q1)
         `unionM`
         eqJoinM pos' posold 
            (return d2) 
            (proj (itemProj cols [mP posold pos, cP descr]) q2)
    qr <- proj (itemProj cols [cP descr, cP pos]) q
    qp1 <- proj [mP posnew pos, mP posold pos'] d1
    qp2 <- proj [mP posnew pos, mP posold pos'] d2
    return $ (DVec qr cols, RVec qp1, RVec qp2)

  vecSegment (DVec q cols) = do
    flip DVec cols <$> proj (itemProj cols [mP descr pos, cP pos]) q

  vecUnsegment (DVec q cols) = do
    qr <- proj (itemProj cols [cP pos, eP descr (ConstE $ nat 1)]) q
    return $ DVec qr cols

  vecDistPrim (DVec q1 cols) (DVec q2 _) = do
    qr <- crossM 
            (proj (map (cP . itemi) cols) q1) 
            (proj [cP descr, cP pos] q2)
    r <- proj [mP posnew pos, mP posold descr] q2
    return (DVec qr cols, PVec r)

  vecDistDesc (DVec q1 cols) (DVec q2 _) = do
    q <- projM (itemProj cols [mP descr pos, mP pos pos'', cP posold])
           $ rownumM pos'' [pos, pos'] Nothing
           $ crossM
               (proj [cP pos] q2)
               (proj (itemProj cols [mP pos' pos, mP posold pos]) q1)
    qr1 <- flip DVec cols <$> proj (itemProj cols [cP descr, cP pos]) q
    qr2 <- PVec <$> proj [cP posold, mP posnew pos] q
    return $ (qr1, qr2)

  vecDistSeg (DVec q1 cols) (DVec q2 _) = do
    q <- eqJoinM pos' descr 
           (proj (itemProj cols [mP pos' pos]) q1) 
           (proj [cP descr, cP pos] q2)
    qr1 <- tagM "distLift/1" $ proj (itemProj cols [cP descr, cP pos]) q
    qr2 <- proj [mP posold pos', mP posnew pos] q
    return $ (DVec qr1 cols, PVec qr2)

  vecLength (DVec d _) = do
    qr <- projM [eP descr (ConstE $ nat 1), eP pos (ConstE $ nat 1), cP item]
          $ aggrM [(Max item, item)] Nothing
          $ (litTable (int 0) item intT)
              `unionM`
              (aggrM [(Count, item)] Nothing $ proj [cP pos] d)
    return $ DVec qr [1]

  vecLengthS (DVec q1 _) (DVec d _) = do
    qr <- rownumM pos [descr] Nothing
            $ aggrM [(Max item, item)] (Just descr)
            $ (proj [mP descr pos, eP item (ConstE $ int 0)] q1)
              `unionM`
              (aggrM [(Count, item)] (Just descr) $ proj [cP descr] d)
    return $ DVec qr [1]

  vecReverse (DVec q cols) = do
    q' <- rownum' pos' [(pos, Desc)] Nothing q
    r <- proj (itemProj cols [cP descr, mP pos pos']) q'
    p <- proj [mP posold pos, mP posnew pos'] q'
    return (DVec r cols, PVec p)

  vecReverseS (DVec q cols) = do
    q' <- rownum' pos' [(descr, Asc), (pos, Desc)] Nothing q
    r <- proj (itemProj cols [cP descr, mP pos pos']) q'
    p <- proj [mP posold pos, mP posnew pos'] q'
    return (DVec r cols, PVec p)

  vecUnique (DVec q cols) = do
    f <- rownumM posnew [posold] Nothing
           $ aggrM [(Min pos, posold)] (Just resCol)
           $ rank resCol [(itemi i, Asc) | i <- cols] q

    qr <- projM (itemProj cols [cP descr, mP pos posnew]) 
          $ eqJoin pos posold q f
    return $ DVec qr cols

  vecUniqueS (DVec q cols) = do
    f <- rownumM posnew [posold] Nothing
           $ aggrM [(Min pos, posold)] (Just resCol)
           $ rank resCol ((descr, Asc):[(itemi i, Asc) | i <- cols]) q
    qr <- projM (itemProj cols [cP descr, mP pos posnew]) 
          $ eqJoin pos posold q f
    return $ DVec qr cols

  vecMin (DVec q _) = do
    qr <- tagM "vecMin" 
          $ projM [eP descr (ConstE $ nat 1), eP pos (ConstE $ nat 1), cP item]
          $ aggr [(Min item, item)] Nothing q
    return $ DVec qr [1]

  vecMax (DVec q _) = do
    qr <- projM [eP descr (ConstE $ nat 1), eP pos (ConstE $ nat 1), cP item]
          $ aggr [(Max item, item)] Nothing q
    return $ DVec qr [1]

  vecMinS (DVec qv _) = do
    qr <- tagM "vecMinLift" $ projM [cP descr,cP pos,cP item]
            $ rownumM pos [descr] Nothing
            $ aggr [(Min item, item)] (Just descr) qv
    return $ DVec qr [1]

  vecMaxS (DVec qv _) = do
    qr <- projM [cP descr,cP pos,cP item]
            $ rownumM pos [descr] Nothing
            $ aggr [(Max item, item)] (Just descr) qv
    return $ DVec qr [1]

  descToRename (DVec q1 _) = RVec <$> proj [mP posnew descr, mP posold pos] q1

  singletonDescr = do
    q <- litTable' [[nat 1, nat 1]] [(descr, natT), (pos, natT)]
    return $ DVec q []

  vecAppend (DVec q1 cols) (DVec q2 _) = do
    q <- rownumM posnew [descr, ordCol, pos] Nothing
           $ projAddCols cols [eP ordCol (ConstE (nat 1))] q1
             `unionM`
             projAddCols cols [eP ordCol (ConstE (nat 2))] q2
    qv <- tagM "append r" (proj (itemProj cols [mP pos posnew, cP descr]) q)
    qp1 <- tagM "append r1"
           $ projM [mP posold pos, mP posnew pos']
           $ select (BinAppE Eq (ColE ordCol) (ConstE $ nat 1)) q
    qp2 <- tagM "append r2"
           $ projM [mP posold pos, mP posnew pos']
           $ select (BinAppE Eq (ColE ordCol) (ConstE $ nat 2)) q
    return $ (DVec qv cols, RVec qp1, RVec qp2)

  vecSum t (DVec q _) = do
    -- the default value for empty lists
    q' <- projM [eP descr (ConstE $ nat 1), eP pos (ConstE $ nat 1), cP item]
            $ case t of
                VL.Int -> litTable (int 0) item intT
                VL.Nat -> litTable (nat 0) item natT
                VL.Double -> litTable (double 0) item doubleT
                _   -> error "This type is not supported by the sum primitive (PF)"
    -- the actual sum
    qs <- projM [eP descr (ConstE $ nat 1), eP pos (ConstE $ nat 1), cP item]
          $ aggrM [(Sum item, item)] Nothing
          $ union q' q
    return $ DVec qs [1]
    
  vecAvg (DVec q _) = do
    qa <- projM [eP descr (ConstE $ nat 1), eP pos (ConstE $ nat 1), cP item]
          $ aggr [(Avg item, item)] Nothing q
    return $ DVec qa [1] 
  
  vecAvgS (DVec _qd _) (DVec qv _) = do
    qa <- projM [cP descr, eP pos (ConstE $ nat 1), cP item]
          $ aggr [(Avg item, item)] (Just descr) qv
    return $ DVec qa [1]

  -- FIXME parameterize the sum operator with its argument type (i.e. double,
  -- int, ...)
  vecSumS (DVec qd _) (DVec qv _) = do
    qe <- projM [cP descr, cP pos, eP item (ConstE (int 0))]
          $ differenceM
            (proj [mP descr pos] qd)
            (proj [cP descr] qv)
    qs <- aggr [(Sum item, item)] (Just descr) qv
    qr <- rownumM pos [descr] Nothing
          $ union qe qs
    -- align the result vector with the original descriptor vector to get
    -- the proper descriptor values (sum removes one list type constructor)
    qa <- projM [mP descr descr', cP pos, cP item]
          $ (eqJoinM pos' descr
             (proj [mP descr' descr, mP pos' pos] qd)
             (return qr))
    return $ DVec qa [1]

  vecSelect expr (DVec q cols) = do
    qs <- projM (itemProj cols [cP descr, mP pos pos']) 
          $ rownumM pos' [pos] Nothing
          $ select (expr1 expr) q
    return $ DVec qs cols

  falsePositions (DVec q1 _) = do
    qr <- projM [cP descr, mP pos pos'', mP item pos']
          $ rownumM pos'' [pos] Nothing
          $ selectM (UnAppE Not (ColE item))
          $ rownum pos' [pos] (Just descr) q1
    return $ DVec qr [1]

  vecTableRef tableName columns keys = do
    q <- -- generate the pos column
         rownumM pos orderCols Nothing
         -- map table columns to item columns, add constant descriptor
         $ projM (eP descr (ConstE (nat 1)) : [ mP c (itemi i) | (c, i) <- numberedColNames ])
         $ dbTable tableName taColumns (map Key keys)
    return $ DVec q (map snd numberedColNames)

    where
      numberedColNames = zipWith (\c i -> (fst c, i)) columns [1..]
      
      taColumns = [ (c, algTy t) | (c, t) <- columns ]

      taKeys = map (\k -> [ itemi $ colIndex c | c <- k ]) keys
      
      colIndex :: AttrName -> Int
      colIndex n =
          case lookup n numberedColNames of
              Just i  -> i
              Nothing -> $impossible
      
      -- the initial table order is generated as follows:
      -- * if there are known keys for the table, we take the shortest one, in the hope
      --   that it will be the primary key. A sorting operation then might be able to
      --   use a primary key index.
      -- * without a key, we just take an arbitrary column (here, the first).
      orderCols = case sortWith length taKeys of
                      k : _ -> k
                      []    -> [itemi 1]

  vecSort (DVec qs colss) (DVec qe colse) = do
    q <- tagM "sortWith"
         $ eqJoinM pos pos''
           (projM [cP pos, cP pos']
              $ rownum pos' (descr : [itemi i | i <- colss] ++ [pos]) Nothing qs)
           (proj (itemProj colse [cP descr, mP pos'' pos]) qe)
    qv <- proj (itemProj colse [cP descr, mP pos pos']) q
    qp <- proj [mP posold pos'', mP posnew pos'] q
    return $ (DVec qv colse, PVec qp)

  vecGroupBy (DVec v1 colsg) (DVec v2 colse) = do 
    q' <- rownumM pos' [resCol, pos] Nothing
            $ rowrank resCol ((descr, Asc):[(itemi i, Asc) | i<- colsg]) v1
    d1 <- distinctM 
          $ proj (itemProj colsg [cP descr, mP pos resCol]) q'
    p <- proj [mP posold pos, mP posnew pos'] q'
    v <- tagM "groupBy ValueVector" 
           $ projM (itemProj colse [cP descr, cP pos])
           $ eqJoinM pos'' pos' (proj [mP descr resCol, mP pos pos', mP pos'' pos] q')
                                (proj ((mP pos' pos):[(mP (itemi i) (itemi i)) | i <- colse]) v2)
    return $ (DVec d1 colsg, DVec v colse, PVec p)

  vecCartProduct (DVec q1 cols1) (DVec q2 cols2) = do
    let itemProj1  = map (cP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)
        itemProj2  = map (cP . itemi) cols2'
    q <- projM ([mP descr pos, cP pos, cP pos', cP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [pos', pos'] Nothing
           $ crossM
             (proj ([cP descr, mP pos' pos] ++ itemProj1) q1)
             (proj ((mP pos'' pos) : shiftProj2) q2)
    qv <- proj ([cP  descr, cP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [mP posold pos', mP posnew pos] q
    qp2 <- proj [mP posold pos'', mP posnew pos] q
    return (DVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)

  vecCartProductS (DVec q1 cols1) (DVec q2 cols2) = do
    let itemProj1  = map (cP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)
        itemProj2  = map (cP . itemi) cols2'
    q <- projM ([mP descr pos, cP pos, cP pos', cP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [descr, descr', pos, pos'] Nothing
           $ eqJoinM descr descr'
             (proj ([cP descr, mP pos' pos] ++ itemProj1) q1)
             (proj ([mP descr' descr, mP pos'' pos] ++ shiftProj2) q2)
    qv <- proj ([cP  descr, cP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [mP posold pos', mP posnew pos] q
    qp2 <- proj [mP posold pos'', mP posnew pos] q
    return (DVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)
    
    
  vecEquiJoin leftExpr rightExpr (DVec q1 cols1) (DVec q2 cols2) = do
    let itemProj1  = map (cP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)
        itemProj2  = map (cP . itemi) cols2'

    q <- projM ([cP descr, cP pos, cP pos', cP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [pos', pos''] Nothing
           $ thetaJoinM [(tmpCol, tmpCol', EqJ)]
             (proj ([ cP descr
                    , mP pos' pos
                    , eP tmpCol (expr1 leftExpr)
                    ] ++ itemProj1) q1)
             (proj ([ mP pos'' pos
                    , eP tmpCol' (expr1 rightExpr)
                    ] ++ shiftProj2) q2)

    qv <- tagM "eqjoin/1" $ proj ([cP  descr, cP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [mP posold pos', mP posnew pos] q
    qp2 <- proj [mP posold pos'', mP posnew pos] q
    return (DVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)
  
  vecEquiJoinS leftExpr rightExpr (DVec q1 cols1) (DVec q2 cols2) = do
    let itemProj1  = map (cP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)
        itemProj2  = map (cP . itemi) cols2'

    q <- projM ([cP descr, cP pos, cP pos', cP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [pos', pos''] Nothing
           $ thetaJoinM [(descr, descr', EqJ), (tmpCol, tmpCol', EqJ)]
             (proj ([ cP descr
                    , mP pos' pos
                    , eP tmpCol (expr1 leftExpr)
                    ] ++ itemProj1) q1)
             (proj ([ mP descr' descr
                    , mP pos'' pos
                    , eP tmpCol' (expr1 rightExpr)
                    ] ++ shiftProj2) q2)

    qv <- proj ([cP  descr, cP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [mP posold pos', mP posnew pos] q
    qp2 <- proj [mP posold pos'', mP posnew pos] q
    return (DVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)
  
  selectPos (DVec qe cols) op (DVec qi _) = do
    qs <- selectM (BinAppE (binOp $ VL.COp op) (ColE pos) (UnAppE (Cast natT) (ColE item')))
          $ crossM 
              (return qe) 
              (proj [mP item' item] qi)

    q' <- case op of
            -- If we select positions from the beginning, we can re-use the old
            -- positions
            VL.Lt  -> projAddCols cols [mP posnew pos] qs
            VL.LtE -> projAddCols cols [mP posnew pos] qs
            -- Only if selected positions don't start at the beginning (i.e. 1)
            -- do we have to recompute them.
            _      -> rownum posnew [pos] Nothing qs
              
    qr <- proj (itemProj cols [cP descr, mP pos posnew]) q'
    qp <- proj [ mP posold pos, cP posnew ] q'
    return $ (DVec qr cols, RVec qp)
  
  selectPosS (DVec qe cols) op (DVec qi _) = do
    qs <- rownumM posnew [pos] Nothing
          $ selectM (BinAppE (binOp $ VL.COp op) (ColE absPos) (UnAppE (Cast natT) (ColE item')))
          $ eqJoinM descr pos'
              (rownum absPos [pos] (Just descr) qe)
              (proj [mP pos' pos, mP item' item] qi)

    qr <- proj (itemProj cols [cP descr, mP pos posnew]) qs
    qp <- proj [ mP posold pos, cP posnew ] qs
    return $ (DVec qr cols, RVec qp)

  selectPos1 (DVec qe cols) op (VL.N posConst) = do
    let posConst' = VNat $ fromIntegral posConst
    qs <- select (BinAppE (binOp $ VL.COp op) (ColE absPos) (ConstE posConst')) qe

    q' <- case op of
            -- If we select positions from the beginning, we can re-use the old
            -- positions
            VL.Lt  -> projAddCols cols [mP posnew pos] qs
            VL.LtE -> projAddCols cols [mP posnew pos] qs
            -- Only if selected positions don't start at the beginning (i.e. 1)
            -- do we have to recompute them.
            _      -> rownum posnew [pos] Nothing qs
              
    qr <- proj (itemProj cols [cP descr, mP pos posnew]) q'
    qp <- proj [ mP posold pos, cP posnew ] q'
    return $ (DVec qr cols, RVec qp)

  -- If we select positions in a lifted way, we need to recompute positions in
  -- any case.
  selectPos1S (DVec qe cols) op (VL.N posConst) = do
    let posConst' = VNat $ fromIntegral posConst
    qs <- rownumM posnew [pos] Nothing
          $ selectM (BinAppE (binOp (VL.COp op)) (ColE absPos) (ConstE posConst'))
          $ rownum absPos [pos] (Just descr) qe
          
    qr <- proj (itemProj cols [cP descr, mP pos posnew]) qs
    qp <- proj [ mP posold pos, cP posnew ] qs
    return $ (DVec qr cols, RVec qp)

  projectRename posnewProj posoldProj (DVec q _) = do
    qn <- rownum pos'' [descr, pos] Nothing q
    qr <- case (posnewProj, posoldProj) of
            (VL.STNumber, VL.STNumber) -> proj [mP posnew pos'', mP posold pos''] qn
            (VL.STNumber, p)           -> proj [mP posnew pos'', transProj posold p] qn
            (p, VL.STNumber)           -> proj [transProj posnew p, mP posold pos''] qn
            (p1, p2)                   -> proj [transProj posnew p1, transProj posold p2] qn

    return $ RVec qr

  vecProject projs (DVec q _) = do
    let projs' = zipWith (\i e -> (itemi i, expr1 e)) [1 .. length projs] projs
    qr <- proj ([cP descr, cP pos] ++ projs') q
    return $ DVec qr [1 .. (length projs)]
    
  vecZipS (DVec q1 cols1) (DVec q2 cols2) = do
    q1' <- rownum pos'' [pos] (Just descr) q1
    q2' <- rownum pos''' [pos] (Just descr) q2
    let offset      = length cols1
        cols2'      = map (+ offset) cols2
        allCols     = cols1 ++ cols2'
        allColsProj = map (cP . itemi) allCols
        shiftProj   = zipWith mP (map itemi cols2') (map itemi cols2)
    qz <- rownumM posnew [descr, pos''] Nothing
          $ projM ([cP pos', cP pos, cP descr] ++ allColsProj)
          $ thetaJoinM [(descr, descr', EqJ), (pos'', pos''', EqJ)]
              (return q1')
              (proj ([mP descr' descr, mP pos' pos, cP pos'''] ++ shiftProj) q2')

    r1 <- proj [mP posold pos'', cP posnew] qz
    r2 <- proj [mP posold pos''', cP posnew] qz
    qr <- proj ([cP descr, mP pos posnew] ++ allColsProj) qz
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
    qr <- projAddCols cols [eP nrItem (UnAppE (Cast natT) (ColE pos))] q
    return $ DVec qr (cols ++ [nrIndex])
  
  -- The Pathfinder implementation of lifted number does not come for free: To
  -- generate the absolute numbers for every sublist (i.e. descriptor
  -- partition), we have to use a partitioned rownumber.
  vecNumberS (DVec q cols) = do
    let nrIndex = length cols + 1
        nrItem = itemi nrIndex
    qr <- rownum nrItem [pos] (Just descr) q
    return $ DVec qr (cols ++ [nrIndex])
  
  vecSemiJoin leftExpr rightExpr (DVec q1 cols1) (DVec q2 _) = do
    q <- rownumM pos [posold] Nothing
         $ projM (itemProj cols1 [cP descr, mP posold pos])
         $ semiJoinM [(tmpCol, tmpCol', EqJ)]
             (proj (itemProj cols1 [cP descr, cP pos, eP tmpCol (expr1 leftExpr)]) q1)
             (proj [mP descr' descr, eP tmpCol' (expr1 rightExpr)] q2)
    qj <- tagM "semijoin/1" $ proj (itemProj cols1 [cP descr, cP pos]) q
    r  <- proj [cP posold, mP posold posnew] q
    return $ (DVec qj cols1, RVec r)
  
  vecSemiJoinS leftExpr rightExpr (DVec q1 cols1) (DVec q2 _) = do
    q <- rownumM pos [descr, posold] Nothing
         $ projM (itemProj cols1 [cP descr, mP posold pos])
         $ semiJoinM [(descr, descr', EqJ), (tmpCol, tmpCol', EqJ)]
             (proj (itemProj cols1 [cP descr, cP pos, eP tmpCol (expr1 leftExpr)]) q1)
             (proj [mP descr' descr, eP tmpCol' (expr1 rightExpr)] q2)
    qj <- tagM "semijoinLift/1" $ proj (itemProj cols1 [cP descr, cP pos]) q
    r  <- proj [cP posold, mP posold posnew] q
    return $ (DVec qj cols1, RVec r)
  
  vecAntiJoin leftExpr rightExpr (DVec q1 cols1) (DVec q2 _) = do
    q <- rownumM pos [posold] Nothing
         $ projM (itemProj cols1 [cP descr, mP posold pos])
         $ antiJoinM [(tmpCol, tmpCol', EqJ)]
             (proj (itemProj cols1 [cP descr, cP pos, eP tmpCol (expr1 leftExpr)]) q1)
             (proj [eP tmpCol' (expr1 rightExpr)] q2)
    qj <- tagM "antijoin/1" $ proj (itemProj cols1 [cP descr, cP pos]) q
    r  <- proj [cP posold, mP posold posnew] q
    return $ (DVec qj cols1, RVec r)
  
  -- FIXME re-check semantics!
  vecAntiJoinS leftExpr rightExpr (DVec q1 cols1) (DVec q2 _) = do
    q <- rownumM pos [descr, posold] Nothing
         $ projM (itemProj cols1 [cP descr, mP posold pos])
         $ antiJoinM [(descr, descr', EqJ), (tmpCol, tmpCol', EqJ)]
             (proj (itemProj cols1 [cP descr, cP pos, eP tmpCol (expr1 leftExpr)]) q1)
             (proj [mP descr' descr, eP tmpCol' (expr1 rightExpr)] q2)
    qj <- tagM "antijoinLift/1" $ proj (itemProj cols1 [cP descr, cP pos]) q
    r  <- proj [cP posold, mP posold posnew] q
    return $ (DVec qj cols1, RVec r)
