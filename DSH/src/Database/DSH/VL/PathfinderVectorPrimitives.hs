{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ParallelListComp     #-}

module Database.DSH.VL.PathfinderVectorPrimitives() where

import           GHC.Exts
       
import           Control.Applicative               hiding (Const)
import qualified Data.List.NonEmpty                as N

import qualified Database.DSH.Common.Lang          as L
import qualified Database.DSH.VL.Lang              as VL
import           Database.DSH.Impossible
import           Database.DSH.VL.Data.DBVector
import           Database.DSH.VL.VectorPrimitives

import           Database.Algebra.Dag.Builder
import           Database.Algebra.Pathfinder
import           Database.Algebra.Pathfinder.Data.Algebra

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

itemProj :: [DBCol] -> [Proj] -> [Proj]
itemProj cols projs = projs ++ [ cP $ itemi i | i <- cols ]

binOp :: L.ScalarBinOp -> BinFun
binOp = $unimplemented
{- FIXME
binOp L.Add  = Plus
binOp L.Sub  = Minus
binOp L.Div  = Div
binOp L.Mul  = Times
binOp L.Mod  = Modulo
binOp L.Eq   = Eq
binOp L.Gt   = Gt
binOp L.GtE  = GtE
binOp L.Lt   = Lt
binOp L.LtE  = LtE
binOp L.Conj = And
binOp L.Disj = Or
binOp L.Like = Like
-}

unOp :: L.ScalarUnOp -> UnFun
unOp = $unimplemented
{- FIXME
unOp L.Not          = Not
unOp (L.CastDouble) = Cast doubleT
unOp L.Sin          = Sin
unOp L.Cos          = Cos
unOp L.Tan          = Tan
unOp L.ASin         = ASin
unOp L.ACos         = ACos
unOp L.ATan         = ATan
unOp L.Sqrt         = Sqrt
unOp L.Exp          = Exp
unOp L.Log          = Log
-}

expr1 :: VL.Expr1 -> Expr
expr1 (VL.BinApp1 op e1 e2) = BinAppE (binOp op) (expr1 e1) (expr1 e2)
expr1 (VL.UnApp1 op e)      = UnAppE (unOp op) (expr1 e)
expr1 (VL.Column1 c)        = ColE $ itemi c
expr1 (VL.Constant1 v)      = ConstE $ algVal v
expr1 (VL.If1 c t e)        = IfE (expr1 c) (expr1 t) (expr1 e)

-- | Vl Expr2 considers two input vectors and may reference columns from the
-- left and right side. Columns from the left map directly to item columns. For
-- right input columns, temporary column names are used.
expr2 :: VL.Expr2 -> Expr
expr2 (VL.BinApp2 op e1 e2)      = BinAppE (binOp op) (expr2 e1) (expr2 e2)
expr2 (VL.UnApp2 op e)           = UnAppE (unOp op) (expr2 e)
expr2 (VL.Column2Left (VL.L c))  = ColE $ itemi c
expr2 (VL.Column2Right (VL.R c)) = ColE $ itemi' c
expr2 (VL.Constant2 v)           = ConstE $ algVal v
expr2 (VL.If2 c t e)             = IfE (expr2 c) (expr2 t) (expr2 e)

colProjection :: VL.Expr1 -> Maybe DBCol
colProjection (VL.Column1 c) = Just c
colProjection _              = Nothing

aggrFun :: VL.AggrFun -> AggrType
aggrFun (VL.AggrSum _ e) = Sum $ expr1 e
aggrFun (VL.AggrMin e)   = Min $ expr1 e
aggrFun (VL.AggrMax e)   = Max $ expr1 e
aggrFun (VL.AggrAvg e)   = Avg $ expr1 e
aggrFun (VL.AggrAll e)   = All $ expr1 e
aggrFun (VL.AggrAny e)   = Any $ expr1 e
aggrFun VL.AggrCount     = Count

-- Common building blocks

-- | For a segmented aggregate operator, apply the aggregate
-- function's default value for the empty segments. The first argument
-- specifies the outer descriptor vector, while the second argument
-- specifies the result vector of the aggregate.
segAggrDefault :: AlgNode -> AlgNode -> AVal -> GraphM r PFAlgebra AlgNode
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
aggrDefault :: AlgNode -> AlgNode -> AVal -> GraphM r PFAlgebra AlgNode
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
sumDefault :: VL.VLType -> (ATy, AVal)
sumDefault VL.Nat    = (ANat, nat 0)
sumDefault VL.Int    = (AInt, int 0)
sumDefault VL.Double = (ADouble, double 0)
sumDefault t         = $impossible

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

  vecAlign (DVec q1 cols1) (DVec q2 cols2) = do
    let cols2'    = [ i + length cols1 | i <- cols2 ]
        shiftProj = [ mP (itemi i') (itemi i) | i <- cols2 | i' <- cols2' ]
        resCols   = cols1 ++ cols2'
    q   <- eqJoinM pos' descr
             (proj (itemProj cols1 [mP pos' pos]) q1)
             (proj ([cP descr, cP pos] ++ shiftProj) q2)

    qr1 <- proj (itemProj resCols [cP descr, cP pos]) q
    qr2 <- proj [mP posold pos', mP posnew pos] q
    return (DVec qr1 resCols, PVec qr2)

  vecAggr a (DVec q _) = do
    -- The aggr operator itself
    qa <- projM [eP descr (ConstE $ nat 1), eP pos (ConstE $ nat 1), cP item] 
          $ aggr [(aggrFun a, item)] [] q
    -- For sum, add the default value for empty inputs
    qd <- case a of
              VL.AggrSum t _ -> aggrDefault q qa (snd $ sumDefault t)
              VL.AggrAll _   -> aggrDefault q qa (bool True)
              VL.AggrAny _   -> aggrDefault q qa (bool False)
              _              -> return qa

    return $ DVec qd [1]

  vecAggrNonEmpty as (DVec q _) = do
    let resCols = [1 .. N.length as]
    
    let aggrFuns = [ (aggrFun a, itemi i)
                   | a <- N.toList as
                   | i <- resCols
                   ]

    qa <- projM (itemProj resCols [eP descr (ConstE $ nat 1), eP pos (ConstE $ nat 1)])
          $ aggr aggrFuns [] q

    return $ DVec qa resCols


  vecAggrS a (DVec qo _) (DVec qi _) = do
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
    return $ DVec qr [1]

  vecAggrNonEmptyS as (DVec qo _) (DVec qi _) = do
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

    return $ DVec qr resCols

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

  vecUniqueS (DVec q cols) = do
    let groupCols = map (\c -> (c, ColE c)) (descr : map itemi cols)
    qr <- rownumM pos [pos] Nothing
          $ aggr [(Min (ColE pos), pos)] groupCols q
    return $ DVec qr cols

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
           $ projM [mP posold pos, cP posnew]
           $ select (BinAppE Eq (ColE ordCol) (ConstE $ nat 1)) q
    qp2 <- tagM "append r2"
           $ projM [mP posold pos, cP posnew]
           $ select (BinAppE Eq (ColE ordCol) (ConstE $ nat 2)) q
    return $ (DVec qv cols, RVec qp1, RVec qp2)

  vecSelect expr (DVec q cols) = do
    qs <- projM (itemProj cols [cP descr, mP pos pos']) 
          $ rownumM pos' [pos] Nothing
          $ select (expr1 expr) q
    return $ DVec qs cols

  vecTableRef tableName columns hints = do
    q <- -- generate the pos column
         rownumM pos orderCols Nothing
         -- map table columns to item columns, add constant descriptor
         $ projM (eP descr (ConstE (nat 1)) : [ mP (itemi i) c | (c, i) <- numberedColNames ])
         $ dbTable tableName taColumns (map Key taKeys)
    return $ DVec q (map snd numberedColNames)

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
    q' <- rownumM pos' [resCol] Nothing
          $ rowrank resCol ((descr, Asc):[(itemi i, Asc) | i<- colsg]) v1
    d1 <- distinctM 
          $ proj (itemProj colsg [cP descr, mP pos resCol]) q'
    p <- proj [mP posold pos, mP posnew pos'] q'
    v <- tagM "groupBy ValueVector" 
           $ projM (itemProj colse [cP descr, cP pos])
           $ eqJoinM pos'' pos' (proj [mP descr resCol, mP pos pos', mP pos'' pos] q')
                                (proj ((mP pos' pos):[(mP (itemi i) (itemi i)) | i <- colse]) v2)
    return $ (DVec d1 colsg, DVec v colse, PVec p)

  vecGroupSimple groupExprs (DVec q1 cols1) = do
      -- apply the grouping expressions and compute surrogate values
      -- from the grouping values
      let groupProjs = [ eP (itemi' i) (expr1 e) | e <- groupExprs | i <- [1..] ]
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

      return (DVec qo [1 .. length groupExprs], DVec qi cols1, PVec qprop)

  vecCartProduct (DVec q1 cols1) (DVec q2 cols2) = do
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
    return (DVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)

  vecCartProductS (DVec q1 cols1) (DVec q2 cols2) = do
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
    return (DVec qv (cols1 ++ cols2'), PVec qp1, PVec qp2)

  -- FIXME merge common parts of vecCartProductS and vecNestProductS
  vecNestProductS (DVec q1 cols1) (DVec q2 cols2) = do
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
    return (DVec qv (cols1 ++ cols2'), PVec qp2)
    
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

  -- There is only one difference between EquiJoinS and NestJoinS. For
  -- NestJoinS, we 'segment' after the join, i.e. use the left input
  -- positions as the result descriptor.
  -- FIXME merge the common parts.
  vecNestJoinS leftExpr rightExpr (DVec q1 cols1) (DVec q2 cols2) = do
    let itemProj1  = map (cP . itemi) cols1
        cols2'     = [((length cols1) + 1) .. ((length cols1) + (length cols2))]
        shiftProj2 = zipWith mP (map itemi cols2') (map itemi cols2)
        itemProj2  = map (cP . itemi) cols2'

    q <- projM ([mP descr pos', cP pos, cP pos', cP pos''] ++ itemProj1 ++ itemProj2)
           $ rownumM pos [descr, pos', pos''] Nothing
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
    qp2 <- proj [mP posold pos'', mP posnew pos] q
    return (DVec qv (cols1 ++ cols2'), PVec qp2)
  
  selectPos (DVec qe cols) op (DVec qi _) = do
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
    qp <- proj [ mP posold pos, cP posnew ] q'
    return $ (DVec qr cols, RVec qp)
  
  selectPosS (DVec qe cols) op (DVec qi _) = do
    qs <- rownumM posnew [pos] Nothing
          $ selectM (BinAppE (binOp op) (ColE absPos) (UnAppE (Cast natT) (ColE item')))
          $ eqJoinM descr pos'
              (rownum absPos [pos] (Just descr) qe)
              (proj [mP pos' pos, mP item' item] qi)

    qr <- proj (itemProj cols [cP descr, mP pos posnew]) qs
    qp <- proj [ mP posold pos, cP posnew ] qs
    return $ (DVec qr cols, RVec qp)

  selectPos1 (DVec qe cols) op (VL.N posConst) = do
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
    return $ (DVec qr cols, RVec qp)

  -- If we select positions in a lifted way, we need to recompute positions in
  -- any case.
  selectPos1S (DVec qe cols) op (VL.N posConst) = do
    let posConst' = VNat $ fromIntegral posConst
    qs <- rownumM posnew [pos] Nothing
          $ selectM (BinAppE (binOp op) (ColE absPos) (ConstE posConst'))
          $ rownum absPos [pos] (Just descr) qe
          
    qr <- proj (itemProj cols [cP descr, mP pos posnew]) qs
    qp <- proj [ mP posold pos, cP posnew ] qs
    return $ (DVec qr cols, RVec qp)

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
  
  vecGroupAggr groupExprs aggrFuns (DVec q _) = do
    let partAttrs = (descr, ColE descr) 
                    : 
                    [ eP (itemi i) (expr1 e) | e <- groupExprs | i <- [1..] ]

        pw = length groupExprs
  
        pfAggrFuns = [ (aggrFun a, itemi $ pw + i) | a <- N.toList aggrFuns | i <- [1..] ]
                 
    qa <- rownumM pos [descr] Nothing
          $ aggr pfAggrFuns partAttrs q

    return $ DVec qa [1 .. length groupExprs + N.length aggrFuns]
  
  vecNumber (DVec q cols) = do
    let nrIndex = length cols + 1
        nrItem = itemi nrIndex
    qr <- projAddCols cols [eP nrItem (UnAppE (Cast natT) (ColE pos))] q
    return $ DVec qr (cols ++ [nrIndex])
  
  -- The Pathfinder implementation of lifted number does not come for
  -- free: To generate the absolute numbers for every sublist
  -- (i.e. descriptor partition), we have to use a partitioned
  -- rownumber.
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
  
  vecAntiJoinS leftExpr rightExpr (DVec q1 cols1) (DVec q2 _) = do
    q <- rownumM pos [descr, posold] Nothing
         $ projM (itemProj cols1 [cP descr, mP posold pos])
         $ antiJoinM [(descr, descr', EqJ), (tmpCol, tmpCol', EqJ)]
             (proj (itemProj cols1 [cP descr, cP pos, eP tmpCol (expr1 leftExpr)]) q1)
             (proj [mP descr' descr, eP tmpCol' (expr1 rightExpr)] q2)
    qj <- tagM "antijoinLift/1" $ proj (itemProj cols1 [cP descr, cP pos]) q
    r  <- proj [cP posold, mP posold posnew] q
    return $ (DVec qj cols1, RVec r)
  
  vecSortSimple sortExprs (DVec q1 cols1) = do
    let sortProjs = zipWith (\i e -> (itemi' i, expr1 e)) [1..] sortExprs
    qs <- rownumM pos' (map fst sortProjs) Nothing
          $ projAddCols cols1 sortProjs q1

    qr1 <- proj (itemProj cols1 [cP descr, mP pos pos']) qs
    qr2 <- proj [mP posold pos, mP posnew pos'] qs

    return (DVec qr1 cols1, PVec qr2)

  -- FIXME none of vecReshape, vecReshapeS, vecTranspose and
  -- vecTransposeS deal with empty inner inputs correctly!
  vecReshape n (DVec q cols) = do
    let dExpr = BinAppE Div (BinAppE Minus (ColE pos) (ConstE $ int 1)) (ConstE $ int $ n + 1)
    qi <- proj (itemProj cols [cP pos, eP descr dExpr]) q
    qo <- projM [eP descr (ConstE $ nat 1), cP pos] 
          $ distinctM 
          $ proj [mP pos descr] qi
    return (DVec qo [], DVec qi cols)

  vecReshapeS n (DVec q cols) = do
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
    
    return (DVec qm [], DVec qi cols) 

  vecTranspose (DVec q cols) = do
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

    return (DVec qo [], DVec qi cols)

  vecTransposeS (DVec qo _) (DVec qi cols) = do
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

    return (DVec qm [], DVec qi' cols)
