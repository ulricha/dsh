{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ParallelListComp      #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Implementation of vector primitives in terms of table algebra
-- operators.
module Database.DSH.VL.TAVectorPrimitives() where

import           Control.Applicative              hiding (Const)
import qualified Data.List.NonEmpty               as N
import           GHC.Exts

import           Database.Algebra.Dag.Build
import           Database.Algebra.Dag.Common
import           Database.Algebra.Table.Construct
import           Database.Algebra.Table.Lang

import qualified Database.DSH.Common.Lang         as L
import           Database.DSH.Impossible
import           Database.DSH.VL.Vector
import qualified Database.DSH.VL.Lang             as VL
import           Database.DSH.VL.VectorPrimitives


--------------------------------------------------------------------------------
-- Some general helpers

-- | Results are stored in column:
pos, item', item, descr, descr', descr'', pos', pos'', pos''', posold, posnew, ordCol, resCol, tmpCol, tmpCol' , absPos, descri, descro, posi, poso:: AttrName
pos       = "pos"
item      = "item1"
item'     = "itemtmp"
descr     = "descr"
descr'    = "descr1"
descr''   = "descr2"
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
descro    = "descro"
descri    = "descri"
poso      = "poso"
posi      = "posi"

itemi :: Int -> AttrName
itemi i = "item" ++ show i

itemi' :: Int -> AttrName
itemi' i = "itemtmp" ++ show i

algVal :: VL.VLVal -> AVal
algVal (VL.VLInt i) = int (fromIntegral i)
algVal (VL.VLBool t) = bool t
algVal VL.VLUnit = int (-1)
algVal (VL.VLString s) = string s
algVal (VL.VLDouble d) = double d
algVal (VL.VLNat n) = nat $ fromIntegral n

algTy :: VL.RowType -> ATy
algTy (VL.Int) = intT
algTy (VL.Double) = doubleT
algTy (VL.Bool) = boolT
algTy (VL.String) = stringT
algTy (VL.Unit) = intT
algTy (VL.Nat) = natT
algTy (VL.Pair _ _) = $impossible

cP :: AttrName -> Proj
cP a = (a, ColE a)

eP :: AttrName -> Expr -> Proj
eP = (,)

mP :: AttrName -> AttrName -> Proj
mP n o = (n, ColE o)

projAddCols :: [DBCol] -> [Proj] -> AlgNode -> Build TableAlgebra AlgNode
projAddCols cols projs q = proj ([cP descr, cP pos] ++ map (cP . itemi) cols ++ projs) q

projAddColsM :: [DBCol] -> [Proj] -> Build TableAlgebra AlgNode -> Build TableAlgebra AlgNode
projAddColsM cols projs mq = do
  q <- mq
  projAddCols cols projs q

projIdentity :: [DBCol] -> AlgNode -> Build TableAlgebra AlgNode
projIdentity cols q = projAddCols cols [cP descr, cP pos] q

itemProj :: [DBCol] -> [Proj] -> [Proj]
itemProj cols projs = projs ++ [ cP $ itemi i | i <- cols ]

binOp :: L.ScalarBinOp -> BinFun
binOp (L.SBNumOp L.Add)     = Plus
binOp (L.SBNumOp L.Sub)     = Minus
binOp (L.SBNumOp L.Div)     = Div
binOp (L.SBNumOp L.Mul)     = Times
binOp (L.SBNumOp L.Mod)     = Modulo
binOp (L.SBRelOp L.Eq)      = Eq
binOp (L.SBRelOp L.NEq)     = NEq
binOp (L.SBRelOp L.Gt)      = Gt
binOp (L.SBRelOp L.GtE)     = GtE
binOp (L.SBRelOp L.Lt)      = Lt
binOp (L.SBRelOp L.LtE)     = LtE
binOp (L.SBBoolOp L.Conj)   = And
binOp (L.SBBoolOp L.Disj)   = Or
binOp (L.SBStringOp L.Like) = Like

unOp :: L.ScalarUnOp -> UnFun
unOp (L.SUBoolOp L.Not)          = Not
unOp (L.SUCastOp (L.CastDouble)) = Cast doubleT
unOp (L.SUNumOp L.Sin)           = Sin
unOp (L.SUNumOp L.Cos)           = Cos
unOp (L.SUNumOp L.Tan)           = Tan
unOp (L.SUNumOp L.ASin)          = ASin
unOp (L.SUNumOp L.ACos)          = ACos
unOp (L.SUNumOp L.ATan)          = ATan
unOp (L.SUNumOp L.Sqrt)          = Sqrt
unOp (L.SUNumOp L.Exp)           = Exp
unOp (L.SUNumOp L.Log)           = Log
unOp L.SUDateOp                  = $unimplemented

taExprOffset :: Int -> VL.Expr -> Expr
taExprOffset o (VL.BinApp op e1 e2) = BinAppE (binOp op) (taExprOffset o e1) (taExprOffset o e2)
taExprOffset o (VL.UnApp op e)      = UnAppE (unOp op) (taExprOffset o e)
taExprOffset o (VL.Column c)        = ColE $ itemi $ c + o
taExprOffset _ (VL.Constant v)      = ConstE $ algVal v
taExprOffset o (VL.If c t e)        = IfE (taExprOffset o c) (taExprOffset o t) (taExprOffset o e)

taExpr :: VL.Expr -> Expr
taExpr = taExprOffset 0

colProjection :: VL.Expr -> Maybe DBCol
colProjection (VL.Column c) = Just c
colProjection _             = Nothing

aggrFun :: VL.AggrFun -> AggrType
aggrFun (VL.AggrSum _ e) = Sum $ taExpr e
aggrFun (VL.AggrMin e)   = Min $ taExpr e
aggrFun (VL.AggrMax e)   = Max $ taExpr e
aggrFun (VL.AggrAvg e)   = Avg $ taExpr e
aggrFun (VL.AggrAll e)   = All $ taExpr e
aggrFun (VL.AggrAny e)   = Any $ taExpr e
aggrFun VL.AggrCount     = Count

-- Common building blocks

-- | For a segmented aggregate operator, apply the aggregate
-- function's default value for the empty segments. The first argument
-- specifies the outer descriptor vector, while the second argument
-- specifies the result vector of the aggregate.
segAggrDefault :: AlgNode -> AlgNode -> AVal -> Build TableAlgebra AlgNode
segAggrDefault qo qa dv =
    return qa
    `unionM`
    projM [cP descr, eP item (ConstE dv)]
        (differenceM
            (proj [mP descr pos] qo)
            (proj [cP descr] qa))

-- | If an aggregate's input is empty, add the aggregate functions
-- default value. The first argument 'q' is the original input vector,
-- whereas the second argument 'qa' is the aggregate's output.
aggrDefault :: AlgNode -> AlgNode -> AVal -> Build TableAlgebra AlgNode
aggrDefault q qa dv = do
    -- If the input is empty, produce a tuple with the default value.
    qd <- projM [eP descr (ConstE $ nat 2), eP pos (ConstE $ nat 1), eP item (ConstE dv)]
          $ (litTable (nat 1) descr ANat)
            `differenceM`
            (proj [cP descr] q)

    -- For an empty input, there will be two tuples in
    -- the union result: the aggregate output with NULL
    -- and the default value.
    qu <- qa `union` qd

    -- Perform an argmax on the descriptor to get either
    -- the sum output (for a non-empty input) or the
    -- default value (which has a higher descriptor).
    projM [eP descr (ConstE $ nat 1), cP pos, cP item]
       $ eqJoinM descr' descr
            (aggr [(Max $ ColE descr, descr')] [] qu)
            (return qu)


-- | The default value for sums over empty lists for all possible
-- numeric input types.
sumDefault :: VL.RowType -> (ATy, AVal)
sumDefault VL.Nat    = (ANat, nat 0)
sumDefault VL.Int    = (AInt, int 0)
sumDefault VL.Double = (ADouble, double 0)
sumDefault _         = $impossible

doZip :: (AlgNode, [DBCol]) -> (AlgNode, [DBCol]) -> Build TableAlgebra (AlgNode, [DBCol])
doZip (q1, cols1) (q2, cols2) = do
  let offset = length cols1
  let cols' = cols1 ++ map (+offset) cols2
  r <- projM (cP descr : cP pos : map (cP . itemi) cols')
         $ eqJoinM pos pos'
           (return q1)
           (proj ((mP pos' pos):[ mP (itemi $ i + offset) (itemi i) | i <- cols2 ]) q2)
  return (r, cols')

joinPredicate :: Int -> L.JoinPredicate VL.Expr -> SemInfJoin
joinPredicate o (L.JoinPred conjs) = N.toList $ fmap joinConjunct conjs
  where
    joinConjunct :: L.JoinConjunct VL.Expr -> (Expr, Expr, JoinRel)
    joinConjunct (L.JoinConjunct e1 op e2) = (taExpr e1, taExprOffset o e2, joinOp op)

    joinOp :: L.BinRelOp -> JoinRel
    joinOp L.Eq  = EqJ
    joinOp L.Gt  = GtJ
    joinOp L.GtE = GeJ
    joinOp L.Lt  = LtJ
    joinOp L.LtE = LeJ
    joinOp L.NEq = NeJ

-- The VectorAlgebra instance for TA algebra

instance VectorAlgebra NDVec TableAlgebra where

  vecZip (ADVec q1 cols1) (ADVec q2 cols2) = do
    (r, cols') <- doZip (q1, cols1) (q2, cols2)
    return $ ADVec r cols'

  vecLit tys vs = do
    qr <- flip litTable' ((descr, natT):(pos, natT):[(itemi i, algTy t) | (i, t) <- zip [1..] tys])
                                 $ map (map algVal) vs
    return $ ADVec qr [1..length tys]

  vecPropRename (RVec q1) (ADVec q2 cols) = do
    q <- tagM "propRename"
         $ projM (itemProj cols [mP descr posnew, cP pos])
         $ eqJoin posold descr q1 q2
    return $ ADVec q cols

  vecPropFilter (RVec q1) (ADVec q2 cols) = do
    q <- rownumM pos' [posnew, pos] Nothing $ eqJoin posold descr q1 q2
    qr1 <- flip ADVec cols <$> proj (itemProj cols [mP descr posnew, mP pos pos']) q
    qr2 <- RVec <$> proj [mP posold pos, mP posnew pos'] q
    return $ (qr1, qr2)

  -- For TA algebra, the filter and reorder cases are the same, since
  -- numbering to generate positions is done with a rownum and involves sorting.
  vecPropReorder (PVec q1) e2 = do
    (p, (RVec r)) <- vecPropFilter (RVec q1) e2
    return (p, PVec r)

  vecUnbox (RVec qu) (ADVec qi cols) = do
    -- Perform a segment join between inner vector and outer unboxing
    -- rename vector. This implicitly discards any unreferenced
    -- segments in qi.
    q <- projM (itemProj cols [mP descr posnew, cP pos, mP posold pos'])
         $ rownumM pos [pos'] Nothing
         $ eqJoinM posold descr'
             (return qu)
             (proj (itemProj cols [mP descr' descr, mP pos' pos]) qi)

    -- The unboxed vector containing one segment from the inner vector.
    qv <- proj (itemProj cols [cP descr, cP pos]) q
    -- A rename vector in case the inner vector has inner vectors as
    -- well.
    qr <- proj [mP posnew pos, cP posold] q

    return (ADVec qv cols, RVec qr)

  vecRestrict (ADVec q1 cols) (ADVec qm _) = do
    q <- rownumM pos'' [pos] Nothing
           $ selectM (ColE resCol)
           $ eqJoinM pos pos' (return q1)
           $ proj [mP pos' pos, mP resCol item] qm
    qr <- tagM "restrictVec/1" $ proj (itemProj cols [mP pos pos'', cP descr]) q
    qp <- proj [mP posold pos, mP posnew pos''] q
    return $ (ADVec qr cols, RVec qp)

  vecCombine (ADVec qb _) (ADVec q1 cols) (ADVec q2 _) = do
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
    return $ (ADVec qr cols, RVec qp1, RVec qp2)

  vecSegment (ADVec q cols) = do
    flip ADVec cols <$> proj (itemProj cols [mP descr pos, cP pos]) q

  vecUnsegment (ADVec q cols) = do
    qr <- proj (itemProj cols [cP pos, eP descr (ConstE $ nat 1)]) q
    return $ ADVec qr cols

  vecDistPrim (ADVec q1 cols) (ADVec q2 _) = do
    qr <- crossM
            (proj (map (cP . itemi) cols) q1)
            (proj [cP descr, cP pos] q2)
    r <- proj [mP posnew pos, mP posold descr] q2
    return (ADVec qr cols, PVec r)

  vecDistDesc (ADVec q1 cols) (ADVec q2 _) = do
    q <- projM (itemProj cols [mP descr pos, mP pos pos'', cP posold])
           $ rownumM pos'' [pos, pos'] Nothing
           $ crossM
               (proj [cP pos] q2)
               (proj (itemProj cols [mP pos' pos, mP posold pos]) q1)
    qr1 <- flip ADVec cols <$> proj (itemProj cols [cP descr, cP pos]) q
    qr2 <- PVec <$> proj [cP posold, mP posnew pos] q
    return $ (qr1, qr2)

  vecAlign (ADVec q1 cols1) (ADVec q2 cols2) = do
    let cols2'    = [ i + length cols1 | i <- cols2 ]
        shiftProj = [ mP (itemi i') (itemi i) | i <- cols2 | i' <- cols2' ]
        resCols   = cols1 ++ cols2'
    q   <- eqJoinM pos' descr
             (proj (itemProj cols1 [mP pos' pos]) q1)
             (proj ([cP descr, cP pos] ++ shiftProj) q2)

    qr1 <- proj (itemProj resCols [cP descr, cP pos]) q
    qr2 <- proj [mP posold pos', mP posnew pos] q
    return (ADVec qr1 resCols, PVec qr2)

  vecAggr a (ADVec q _) = do
    -- The aggr operator itself
    qa <- projM [eP descr (ConstE $ nat 1), eP pos (ConstE $ nat 1), cP item]
          $ aggr [(aggrFun a, item)] [] q
    -- For sum, add the default value for empty inputs
    qd <- case a of
              VL.AggrSum t _ -> aggrDefault q qa (snd $ sumDefault t)
              VL.AggrAll _   -> aggrDefault q qa (bool True)
              VL.AggrAny _   -> aggrDefault q qa (bool False)
              _              -> return qa

    return $ ADVec qd [1]

  vecAggrNonEmpty as (ADVec q _) = do
    let resCols = [1 .. N.length as]

    let aggrFuns = [ (aggrFun a, itemi i)
                   | a <- N.toList as
                   | i <- resCols
                   ]

    qa <- projM (itemProj resCols [eP descr (ConstE $ nat 1), eP pos (ConstE $ nat 1)])
          $ aggr aggrFuns [] q

    return $ ADVec qa resCols


  vecAggrS a (ADVec qo _) (ADVec qi _) = do
    qa <- aggr [(aggrFun a, item)] [(descr, ColE descr)] qi
    qd <- case a of
              VL.AggrSum t _ -> segAggrDefault qo qa (snd $ sumDefault t)
              VL.AggrAny _   -> segAggrDefault qo qa (bool False)
              VL.AggrAll _   -> segAggrDefault qo qa (bool True)

              VL.AggrCount   -> segAggrDefault qo qa (int 0)
              _              -> return qa

    -- We have to unnest the inner vector (i.e. surrogate join) to get
    -- the outer descriptor values (segmented aggregates remove one
    -- list type constructor)
    qr <- projM [mP descr descr', mP pos pos', cP item]
          $ (eqJoinM pos' descr
             (proj [mP descr' descr, mP pos' pos] qo)
             (return qd))
    return $ ADVec qr [1]

  vecAggrNonEmptyS as (ADVec qo _) (ADVec qi _) = do
    let resCols = [1 .. N.length as]

    let aggrFuns = [ (aggrFun a, itemi i)
                   | a <- N.toList as
                   | i <- resCols
                   ]

    -- Compute aggregate output per segment and new positions
    qa <- projM (itemProj resCols [cP descr, cP pos])
          $ rownumM pos [descr] Nothing
          $ aggr aggrFuns [(descr, ColE descr)] qi

    -- Remove one level of nesting.
    qr <- projM (itemProj resCols [mP descr descr', cP pos])
          $ eqJoinM pos' descr
             (proj [mP descr' descr, mP pos' pos] qo)
             (return qa)

    return $ ADVec qr resCols

  vecReverse (ADVec q cols) = do
    q' <- rownum' pos' [(pos, Desc)] Nothing q
    r <- proj (itemProj cols [cP descr, mP pos pos']) q'
    p <- proj [mP posold pos, mP posnew pos'] q'
    return (ADVec r cols, PVec p)

  vecReverseS (ADVec q cols) = do
    q' <- rownum' pos' [(descr, Asc), (pos, Desc)] Nothing q
    r <- proj (itemProj cols [cP descr, mP pos pos']) q'
    p <- proj [mP posold pos, mP posnew pos'] q'
    return (ADVec r cols, PVec p)

  vecUniqueS (ADVec q cols) = do
    let groupCols = map (\c -> (c, ColE c)) (descr : map itemi cols)
    qr <- rownumM pos [pos] Nothing
          $ aggr [(Min (ColE pos), pos)] groupCols q
    return $ ADVec qr cols

  descToRename (ADVec q1 _) = RVec <$> proj [mP posnew descr, mP posold pos] q1

  singletonDescr = do
    q <- litTable' [[nat 1, nat 1]] [(descr, natT), (pos, natT)]
    return $ ADVec q []

  vecAppend (ADVec q1 cols) (ADVec q2 _) = do
    q <- rownumM posnew [ordCol, pos] Nothing
           $ projAddCols cols [eP ordCol (ConstE (nat 1))] q1
             `unionM`
             projAddCols cols [eP ordCol (ConstE (nat 2))] q2
    qv <- tagM "append r" (proj (itemProj cols [mP pos posnew, cP descr]) q)
    qp1 <- tagM "append r1"
           $ projM [mP posold pos, cP posnew]
           $ select (BinAppE Eq (ColE ordCol) (ConstE $ nat 1)) q
    qp2 <- tagM "append r2"
           $ projM [mP posold pos, cP posnew]
           $ select (BinAppE Eq (ColE ordCol) (ConstE $ nat 2)) q
    return $ (ADVec qv cols, RVec qp1, RVec qp2)

  vecAppendS (ADVec q1 cols) (ADVec q2 _) = do
    q <- rownumM posnew [descr, ordCol, pos] Nothing
           $ projAddCols cols [eP ordCol (ConstE (nat 1))] q1
             `unionM`
             projAddCols cols [eP ordCol (ConstE (nat 2))] q2
    qv <- tagM "append r" (proj (itemProj cols [mP pos posnew, cP descr]) q)
    qp1 <- tagM "append r1"
           $ projM [mP posold pos, cP posnew]
           $ select (BinAppE Eq (ColE ordCol) (ConstE $ nat 1)) q
    qp2 <- tagM "append r2"
           $ projM [mP posold pos, cP posnew]
           $ select (BinAppE Eq (ColE ordCol) (ConstE $ nat 2)) q
    return $ (ADVec qv cols, RVec qp1, RVec qp2)

  vecSelect expr (ADVec q cols) = do
    qs <- rownumM posnew [pos] Nothing
          $ select (taExpr expr) q
    qv <- proj (itemProj cols [cP descr, mP pos posnew]) qs
    qr <- proj [mP posold pos, cP posnew] qs
    return (ADVec qv cols, RVec qr)

  vecTableRef tableName columns hints = do
    q <- -- generate the pos column
         rownumM pos orderCols Nothing
         -- map table columns to item columns, add constant descriptor
         $ projM (eP descr (ConstE (nat 1)) : [ mP (itemi i) c | (c, i) <- numberedColNames ])
         $ dbTable tableName taColumns (map Key taKeys)
    return $ ADVec q (map snd numberedColNames)

    where
      numberedColNames = zipWith (\((L.ColName c), _) i -> (c, i)) columns [1..]

      taColumns = [ (c, algTy t) | (L.ColName c, t) <- columns ]

      taKeys =    [ [ itemi $ colIndex c | L.ColName c <- k ] | L.Key k <- L.keysHint hints ]

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

  vecSortS (ADVec qs colss) (ADVec qe colse) = do
    q <- tagM "sortWith"
         $ eqJoinM pos pos''
           (projM [cP pos, cP pos']
              $ rownum pos' (descr : [itemi i | i <- colss] ++ [pos]) Nothing qs)
           (proj (itemProj colse [cP descr, mP pos'' pos]) qe)
    qv <- proj (itemProj colse [cP descr, mP pos pos']) q
    qp <- proj [mP posold pos'', mP posnew pos'] q
    return $ (ADVec qv colse, PVec qp)

  vecGroupBy (ADVec v1 colsg) (ADVec v2 colse) = do
    q' <- rownumM pos' [resCol] Nothing
          $ rowrank resCol ((descr, Asc):[(itemi i, Asc) | i<- colsg]) v1
    d1 <- distinctM
          $ proj (itemProj colsg [cP descr, mP pos resCol]) q'
    p <- proj [mP posold pos, mP posnew pos'] q'
    v <- tagM "groupBy ValueVector"
           $ projM (itemProj colse [cP descr, cP pos])
           $ eqJoinM pos'' pos' (proj [mP descr resCol, mP pos pos', mP pos'' pos] q')
                                (proj ((mP pos' pos):[(mP (itemi i) (itemi i)) | i <- colse]) v2)
    return $ (ADVec d1 colsg, ADVec v colse, PVec p)

  vecGroupScalarS groupExprs (ADVec q1 cols1) = do
      -- apply the grouping expressions and compute surrogate values
      -- from the grouping values
      let groupProjs = [ eP (itemi' i) (taExpr e) | e <- groupExprs | i <- [1..] ]
          groupCols = map fst groupProjs
      qg <- rowrankM resCol [ (c, Asc) | c <- (descr : groupCols) ]
            $ proj (itemProj cols1 (cP descr : groupProjs)) q1

      -- Create the outer vector, containing surrogate values and the
      -- grouping values
      qo <- distinctM
            $ proj ([cP descr, mP pos resCol]
                    ++ [ mP (itemi i) c | c <- groupCols | i <- [1..] ]) qg

      -- Create new positions for the inner vector
      qp <- rownum posnew [resCol] Nothing qg

      -- Create the inner vector, containing the actual groups
      qi <- proj (itemProj cols1 [mP descr resCol, mP pos posnew]) qp

      qprop <- proj [mP posold pos, cP posnew] qp

      return (ADVec qo [1 .. length groupExprs], ADVec qi cols1, PVec qprop)

  vecCartProduct (ADVec q1 cols1) (ADVec q2 cols2) = do
    let itemProj1  = map (cP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)
        itemProj2  = map (cP . itemi) cols2'

    q <- projM ([cP descr, cP pos, cP pos', cP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [pos', pos''] Nothing
           $ crossM
             (proj ([cP descr, mP pos' pos] ++ itemProj1) q1)
             (proj ((mP pos'' pos) : shiftProj2) q2)

    qv <- proj ([cP  descr, cP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [mP posold pos', mP posnew pos] q
    qp2 <- proj [mP posold pos'', mP posnew pos] q
    return (ADVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)

  vecCartProductS (ADVec q1 cols1) (ADVec q2 cols2) = do
    let itemProj1  = map (cP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)
        itemProj2  = map (cP . itemi) cols2'
    q <- projM ([cP descr, cP pos, cP pos', cP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [descr, descr', pos', pos''] Nothing
           $ eqJoinM descr descr'
             (proj ([cP descr, mP pos' pos] ++ itemProj1) q1)
             (proj ([mP descr' descr, mP pos'' pos] ++ shiftProj2) q2)
    qv <- proj ([cP  descr, cP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [mP posold pos', mP posnew pos] q
    qp2 <- proj [mP posold pos'', mP posnew pos] q
    return (ADVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)

  -- FIXME merge common parts of vecCartProductS and vecNestProductS
  vecNestProductS (ADVec q1 cols1) (ADVec q2 cols2) = do
    let itemProj1  = map (cP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)
        itemProj2  = map (cP . itemi) cols2'

    q <- projM ([mP descr pos', cP pos, cP pos', cP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [descr, pos', pos''] Nothing
           $ eqJoinM descr descr'
             (proj ([cP descr, mP pos' pos] ++ itemProj1) q1)
             (proj ([mP descr' descr, mP pos'' pos] ++ shiftProj2) q2)
    qv <- proj ([cP  descr, cP pos] ++ itemProj1 ++ itemProj2) q
    qp2 <- proj [mP posold pos'', mP posnew pos] q
    return (ADVec qv (cols1 ++ cols2'), PVec qp2)

  vecThetaJoin joinPred (ADVec q1 cols1) (ADVec q2 cols2) = do
    let itemProj1  = map (cP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)
        itemProj2  = map (cP . itemi) cols2'

    q <- projM ([cP descr, cP pos, cP pos', cP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [pos', pos''] Nothing
           $ thetaJoinM (joinPredicate (length cols1) joinPred)
             (proj ([ cP descr
                    , mP pos' pos
                    ] ++ itemProj1) q1)
             (proj ([ mP pos'' pos
                    ] ++ shiftProj2) q2)

    qv <- tagM "eqjoin/1" $ proj ([cP  descr, cP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [mP posold pos', mP posnew pos] q
    qp2 <- proj [mP posold pos'', mP posnew pos] q
    return (ADVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)

  vecThetaJoinS joinPred (ADVec q1 cols1) (ADVec q2 cols2) = do
    let itemProj1  = map (cP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)
        itemProj2  = map (cP . itemi) cols2'

    q <- projM ([cP descr, cP pos, cP pos', cP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [pos', pos''] Nothing
           $ thetaJoinM ((ColE descr, ColE descr', EqJ) : joinPredicate (length cols1) joinPred)
             (proj ([ cP descr
                    , mP pos' pos
                    ] ++ itemProj1) q1)
             (proj ([ mP descr' descr
                    , mP pos'' pos
                    ] ++ shiftProj2) q2)

    qv <- proj ([cP  descr, cP pos] ++ itemProj1 ++ itemProj2) q
    qp1 <- proj [mP posold pos', mP posnew pos] q
    qp2 <- proj [mP posold pos'', mP posnew pos] q
    return (ADVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)

  -- There is only one difference between EquiJoinS and NestJoinS. For
  -- NestJoinS, we 'segment' after the join, i.e. use the left input
  -- positions as the result descriptor.
  -- FIXME merge the common parts.
  vecNestJoinS joinPred (ADVec q1 cols1) (ADVec q2 cols2) = do
    let itemProj1  = map (cP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)
        itemProj2  = map (cP . itemi) cols2'

    q <- projM ([mP descr pos', cP pos, cP pos', cP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [descr, pos', pos''] Nothing
           $ thetaJoinM ((ColE descr, ColE descr', EqJ) : joinPredicate (length cols1) joinPred)
             (proj ([ cP descr
                    , mP pos' pos
                    ] ++ itemProj1) q1)
             (proj ([ mP descr' descr
                    , mP pos'' pos
                    ] ++ shiftProj2) q2)

    qv <- proj ([cP  descr, cP pos] ++ itemProj1 ++ itemProj2) q
    qp2 <- proj [mP posold pos'', mP posnew pos] q
    return (ADVec qv (cols1 ++ cols2'), PVec qp2)

  vecSelectPos (ADVec qe cols) op (ADVec qi _) = do
    qs <- selectM (BinAppE (binOp op) (ColE pos) (UnAppE (Cast natT) (ColE item')))
          $ crossM
              (return qe)
              (proj [mP item' item] qi)

    q' <- case op of
            -- If we select positions from the beginning, we can re-use the old
            -- positions
            (L.SBRelOp L.Lt)  -> projAddCols cols [mP posnew pos] qs
            (L.SBRelOp L.LtE) -> projAddCols cols [mP posnew pos] qs
            -- Only if selected positions don't start at the beginning (i.e. 1)
            -- do we have to recompute them.
            _      -> rownum posnew [pos] Nothing qs

    qr <- proj (itemProj cols [cP descr, mP pos posnew]) q'
    -- A regular rename vector for re-aligning inner vectors
    qp <- proj [ mP posold pos, cP posnew ] q'
    -- An unboxing rename vector
    qu <- proj [ mP posold pos, mP posnew descr ] q'
    return $ (ADVec qr cols, RVec qp, RVec qu)

  vecSelectPosS (ADVec qe cols) op (ADVec qi _) = do
    qs <- rownumM posnew [pos] Nothing
          $ selectM (BinAppE (binOp op) (ColE absPos) (UnAppE (Cast natT) (ColE item')))
          $ eqJoinM descr pos'
              (rownum absPos [pos] (Just descr) qe)
              (proj [mP pos' pos, mP item' item] qi)

    qr <- proj (itemProj cols [cP descr, mP pos posnew]) qs
    qp <- proj [ mP posold pos, cP posnew ] qs
    qu <- proj [ mP posnew descr, mP posold pos] qs
    return $ (ADVec qr cols, RVec qp, RVec qu)

  vecSelectPos1 (ADVec qe cols) op (VL.N posConst) = do
    let posConst' = VNat $ fromIntegral posConst
    qs <- select (BinAppE (binOp op) (ColE pos) (ConstE posConst')) qe

    q' <- case op of
            -- If we select positions from the beginning, we can re-use the old
            -- positions
            (L.SBRelOp L.Lt)  -> projAddCols cols [mP posnew pos] qs
            (L.SBRelOp L.LtE) -> projAddCols cols [mP posnew pos] qs
            -- Only if selected positions don't start at the beginning (i.e. 1)
            -- do we have to recompute them.
            _      -> rownum posnew [pos] Nothing qs

    qr <- proj (itemProj cols [cP descr, mP pos posnew]) q'
    qp <- proj [ mP posold pos, cP posnew ] q'
    qu <- proj [ mP posold pos, mP posnew descr ] q'
    return $ (ADVec qr cols, RVec qp, RVec qu)

  -- If we select positions in a lifted way, we need to recompute
  -- positions in any case.
  vecSelectPos1S (ADVec qe cols) op (VL.N posConst) = do
    let posConst' = VNat $ fromIntegral posConst
    qs <- rownumM posnew [pos] Nothing
          $ selectM (BinAppE (binOp op) (ColE absPos) (ConstE posConst'))
          $ rownum absPos [pos] (Just descr) qe

    qr <- proj (itemProj cols [cP descr, mP pos posnew]) qs
    qp <- proj [ mP posold pos, cP posnew ] qs
    qu <- proj [ mP posold pos, mP posnew descr ] qs
    return $ (ADVec qr cols, RVec qp, RVec qu)

  vecProject projs (ADVec q _) = do
    let projs' = zipWith (\i e -> (itemi i, taExpr e)) [1 .. length projs] projs
    qr <- proj ([cP descr, cP pos] ++ projs') q
    return $ ADVec qr [1 .. (length projs)]

  vecZipS (ADVec q1 cols1) (ADVec q2 cols2) = do
    q1' <- rownum pos'' [pos] (Just descr) q1
    q2' <- rownum pos''' [pos] (Just descr) q2
    let offset      = length cols1
        cols2'      = map (+ offset) cols2
        allCols     = cols1 ++ cols2'
        allColsProj = map (cP . itemi) allCols
        shiftProj   = zipWith mP (map itemi cols2') (map itemi cols2)
    qz <- rownumM posnew [descr, pos''] Nothing
          $ projM ([cP pos', cP pos, cP descr] ++ allColsProj)
          $ thetaJoinM [(ColE descr, ColE descr', EqJ), (ColE pos'', ColE pos''', EqJ)]
              (return q1')
              (proj ([mP descr' descr, mP pos' pos, cP pos'''] ++ shiftProj) q2')

    r1 <- proj [mP posold pos'', cP posnew] qz
    r2 <- proj [mP posold pos''', cP posnew] qz
    qr <- proj ([cP descr, mP pos posnew] ++ allColsProj) qz
    return (ADVec qr allCols, RVec r1, RVec r2)

  vecGroupAggr groupExprs aggrFuns (ADVec q _) = do
    let partAttrs = (descr, ColE descr)
                    :
                    [ eP (itemi i) (taExpr e) | e <- groupExprs | i <- [1..] ]

        pw = length groupExprs

        pfAggrFuns = [ (aggrFun a, itemi $ pw + i) | a <- N.toList aggrFuns | i <- [1..] ]

    qa <- rownumM pos [descr] Nothing
          $ aggr pfAggrFuns partAttrs q

    return $ ADVec qa [1 .. length groupExprs + N.length aggrFuns]

  vecNumber (ADVec q cols) = do
    let nrIndex = length cols + 1
        nrItem = itemi nrIndex
    qr <- projAddCols cols [eP nrItem (UnAppE (Cast natT) (ColE pos))] q
    return $ ADVec qr (cols ++ [nrIndex])

  -- The TA implementation of lifted number does not come for
  -- free: To generate the absolute numbers for every sublist
  -- (i.e. descriptor partition), we have to use a partitioned
  -- rownumber.
  vecNumberS (ADVec q cols) = do
    let nrIndex = length cols + 1
        nrItem = itemi nrIndex
    qr <- rownum nrItem [pos] (Just descr) q
    return $ ADVec qr (cols ++ [nrIndex])

  vecSemiJoin joinPred (ADVec q1 cols1) (ADVec q2 cols2) = do
    let cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)

    q <- rownumM pos [posold] Nothing
         $ projM (itemProj cols1 [cP descr, mP posold pos])
         $ semiJoinM (joinPredicate (length cols1) joinPred)
             (proj (itemProj cols1 [cP descr, cP pos]) q1)
             (proj shiftProj2 q2)
    qj <- tagM "semijoin/1" $ proj (itemProj cols1 [cP descr, cP pos]) q
    r  <- proj [cP posold, mP posold posnew] q
    return $ (ADVec qj cols1, RVec r)

  vecSemiJoinS joinPred (ADVec q1 cols1) (ADVec q2 cols2) = do
    let cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)

    q <- rownumM pos [descr, posold] Nothing
         $ projM (itemProj cols1 [cP descr, mP posold pos])
         $ semiJoinM ((ColE descr, ColE descr', EqJ) : joinPredicate (length cols1) joinPred)
             (proj (itemProj cols1 [cP descr, cP pos]) q1)
             (proj ([mP descr' descr] ++ shiftProj2) q2)
    qj <- tagM "semijoinLift/1" $ proj (itemProj cols1 [cP descr, cP pos]) q
    r  <- proj [cP posold, mP posold posnew] q
    return $ (ADVec qj cols1, RVec r)

  vecAntiJoin joinPred (ADVec q1 cols1) (ADVec q2 cols2) = do
    let cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)

    q <- rownumM pos [posold] Nothing
         $ projM (itemProj cols1 [cP descr, mP posold pos])
         $ antiJoinM (joinPredicate (length cols1) joinPred)
             (proj (itemProj cols1 [cP descr, cP pos]) q1)
             (proj shiftProj2 q2)
    qj <- tagM "antijoin/1" $ proj (itemProj cols1 [cP descr, cP pos]) q
    r  <- proj [cP posold, mP posold posnew] q
    return $ (ADVec qj cols1, RVec r)

  vecAntiJoinS joinPred (ADVec q1 cols1) (ADVec q2 cols2) = do
    let cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)

    q <- rownumM pos [descr, posold] Nothing
         $ projM (itemProj cols1 [cP descr, mP posold pos])
         $ antiJoinM ((ColE descr, ColE descr', EqJ) : joinPredicate (length cols1) joinPred)
             (proj (itemProj cols1 [cP descr, cP pos]) q1)
             (proj ([mP descr' descr] ++ shiftProj2) q2)
    qj <- tagM "antijoinLift/1" $ proj (itemProj cols1 [cP descr, cP pos]) q
    r  <- proj [cP posold, mP posold posnew] q
    return $ (ADVec qj cols1, RVec r)

  vecSortScalarS sortExprs (ADVec q1 cols1) = do
    let sortProjs = zipWith (\i e -> (itemi' i, taExpr e)) [1..] sortExprs
    qs <- rownumM pos' (map fst sortProjs) Nothing
          $ projAddCols cols1 sortProjs q1

    qr1 <- proj (itemProj cols1 [cP descr, mP pos pos']) qs
    qr2 <- proj [mP posold pos, mP posnew pos'] qs

    return (ADVec qr1 cols1, PVec qr2)

  -- FIXME none of vecReshape, vecReshapeS, vecTranspose and
  -- vecTransposeS deal with empty inner inputs correctly!
  vecReshape n (ADVec q cols) = do
    let dExpr = BinAppE Div (BinAppE Minus (ColE pos) (ConstE $ int 1)) (ConstE $ int $ n + 1)
    qi <- proj (itemProj cols [cP pos, eP descr dExpr]) q
    qo <- projM [eP descr (ConstE $ nat 1), cP pos]
          $ distinctM
          $ proj [mP pos descr] qi
    return (ADVec qo [], ADVec qi cols)

  vecReshapeS n (ADVec q cols) = do
    let dExpr = BinAppE Div (BinAppE Minus (ColE absPos) (ConstE $ int 1)) (ConstE $ int $ n + 1)
    qr <- -- Make the new descriptors valid globally
          -- FIXME need a rowrank instead!
          rownumM descr'' [descr, descr'] Nothing
          -- Assign the inner list elements to sublists. Generated
          -- descriptors are _per_ inner list!
          $ projM (itemProj cols [cP descr, cP pos, eP descr' dExpr])
          -- Generate absolute positions for the inner lists
          $ rownum absPos [pos] (Just descr) q

    -- We can compute the 'middle' descriptor vector from the original
    -- inner vector.
    qm <- distinctM $ proj [cP descr, mP pos descr''] qr

    qi <- proj (itemProj cols [mP descr descr'', cP pos]) qr

    return (ADVec qm [], ADVec qi cols)

  vecTranspose (ADVec q cols) = do
    qi <- projM (itemProj cols [mP descr descr', mP pos pos'])
          -- Generate new positions. We use absolute positions as the
          -- new descriptor here. This implements the swapping of row
          -- and column ids (here: descr and pos) that is the core of
          -- transposition.
          $ rownumM pos' [descr', pos] Nothing
          -- Generate absolute positions for the inner lists
          $ rownum descr' [pos] (Just descr) q

    qo <- projM [eP descr (ConstE $ nat 1), cP pos]
          $ distinctM
          $ proj [mP pos descr] qi

    return (ADVec qo [], ADVec qi cols)

  vecTransposeS (ADVec qo _) (ADVec qi cols) = do
    qr  <- -- Generate new globally valid positions for the inner vector
           rownumM pos' [descr', absPos] Nothing
           -- Absolute positions form the new inner descriptor. However, so
           -- far they are relative to the outer descriptor. Here, make them
           -- "globally" valid.
           $ rowrankM descr' [(descro, Asc), (absPos, Asc)]
           -- As usual, generate absolute positions
           $ rownumM absPos [posi] (Just descri)
           -- Join middle and inner vector because we need to know to which
           -- outer list each leaf element belongs
           $ eqJoinM poso descri
               (proj [mP descro descr, mP poso pos] qo)
               (proj (itemProj cols [mP descri descr, mP posi pos]) qi)

    qi' <- proj (itemProj cols [mP descr descr', mP pos pos']) qr
    qm  <- distinctM $ proj [mP descr descro, mP pos descr'] qr

    return (ADVec qm [], ADVec qi' cols)
