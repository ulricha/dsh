{-# LANGUAGE ExplicitForAll      #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE BangPatterns        #-}

module Database.DSH.Execute
    ( execQueryBundle
    ) where

import qualified Data.Sequence as S
import           Control.Monad.State
import qualified Data.HashMap.Strict              as M
import           Data.List
import qualified Data.Vector                      as V
import           Text.Printf

import           Database.DSH.Common.Pretty
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector

import           Database.DSH.Backend
import           Database.DSH.Common.Impossible
import           Database.DSH.Execute.TH
import qualified Database.DSH.Frontend.Internals  as F

------------------------------------------------------------------------------
-- Segment Layouts

-- Generate the definition for the 'SegTuple' type
$(mkSegTupleType 16)

-- | A map from segment descriptor to list value expressions
type SegMap a = M.HashMap CompositeKey (F.Exp a)

-- | Row layout with nesting data in the form of segment maps
data SegLayout a where
    SCol   :: !(F.Type a) -> !ColName -> SegLayout a
    SNest  :: F.Reify a => !(F.Type [a]) -> !(SegMap [a]) -> SegLayout [a]
    STuple :: !(SegTuple a) -> SegLayout a

--------------------------------------------------------------------------------
-- Turn layouts into layouts with explicit column names

data ColLayout q = CCol ColName
                 | CNest q (ColLayout q)
                 | CTuple [ColLayout q]

-- | Annotate every column reference with its column index in a flat
-- column layout.
columnIndexes :: RelationalVector v => V.Vector ColName -> Layout v -> ColLayout v
columnIndexes itemCols lyt = evalState (numberCols itemCols lyt) 1

numberCols :: RelationalVector v => V.Vector ColName -> Layout v -> State Int (ColLayout v)
numberCols itemCols LCol          = currentCol >>= \i -> return (CCol $ itemCols V.! (i - 1))
numberCols itemCols (LTuple lyts) = CTuple <$> mapM (numberCols itemCols) lyts
numberCols _        (LNest q lyt) = CNest q <$> posBracket (numberCols (rvItemCols q) lyt)

currentCol :: State Int Int
currentCol = do
    i <- get
    put $ i + 1
    return i

posBracket :: State Int (ColLayout q) -> State Int (ColLayout q)
posBracket ma = do
    c <- get
    put 1
    a <- ma
    put c
    return a

--------------------------------------------------------------------------------
-- Execute flat queries and construct result values

execQueryBundle :: Backend c
                => c
                -> Shape (BackendCode c)
                -> F.Type a
                -> IO (F.Exp a)
execQueryBundle !conn !shape !ty =
    transactionally conn $ \conn' ->
    case (shape, ty) of
        (VShape q lyt, F.ListT ety) -> do
            slyt <- execNested conn' (columnIndexes (rvItemCols q) lyt) ety
            tab  <- execFlatQuery conn' q
            return $! F.ListE (foldl' (vecIter (rvKeyCols q) slyt) S.empty tab)
        (SShape q lyt, _) -> do
            tlyt <- execNested conn' (columnIndexes (rvItemCols q) lyt) ty
            tab  <- execFlatQuery conn' q
            return $! fromPrim tab (rvKeyCols q) tlyt
        _ -> $impossible

-- | Traverse the layout and execute all subqueries for nested vectors
execNested :: Backend c
           => c -> ColLayout (BackendCode c)
           -> F.Type a
           -> IO (SegLayout a)
execNested !conn lyt ty =
    case (lyt, ty) of
        (CCol i, t)                   -> return $ SCol t i
        (CNest q clyt, F.ListT t)     -> do
            clyt' <- execNested conn clyt t
            tab   <- execFlatQuery conn q
            return (SNest ty (mkSegMap (rvKeyCols q) (rvRefCols q) tab clyt'))
        (CTuple lyts, F.TupleT tupTy) -> let execTuple = $(mkExecTuple 16)
                                         in execTuple lyts tupTy
        (_, _)                        ->
            error $ printf "Type does not match query structure: %s" (pp ty)

------------------------------------------------------------------------------
-- Construct result value terms from raw tabular results

-- | Construct one element value of the result list from a single row
-- of the outer vector.
vecIter :: Row r
        => [ColName]
        -> SegLayout a
        -> S.Seq (F.Exp a)
        -> r
        -> S.Seq (F.Exp a)
vecIter !keyCols !slyt !vals !row =
    let !val = constructVal keyCols slyt row
    in vals S.|> val

-- | Construct a single value from an outer vector
fromPrim :: Row r => [r] -> [ColName] -> SegLayout a -> F.Exp a
fromPrim tab keyCols slyt =
    case tab of
        [!row] -> constructVal keyCols slyt row
        _      -> $impossible

------------------------------------------------------------------------------
-- Construct nested result values from segmented vectors

data SegAcc a = SegAcc
    { saCurrSeg :: !CompositeKey
    , saSegMap  :: !(SegMap [a])
    , saCurrVec :: !(S.Seq (F.Exp a))
    }

-- | Construct a segment map from a segmented vector
mkSegMap :: (F.Reify a, Row r)
         => [ColName]
         -> [ColName]
         -> [r]
         -> SegLayout a
         -> SegMap [a]
mkSegMap !keyCols !refCols !tab !slyt =
    let -- FIXME using the empty list as the starting key is not exactly nice
        !initialAcc = SegAcc { saCurrSeg = (CompositeKey [])
                             , saSegMap  = M.empty
                             , saCurrVec = S.empty
                             }
        !finalAcc = foldl' (segIter keyCols refCols slyt) initialAcc tab
    in M.insert (saCurrSeg finalAcc)
                (F.ListE $ saCurrVec finalAcc)
                (saSegMap finalAcc)

-- | Fold iterator that constructs a map from segment descriptor to
-- the list value that is represented by that segment
segIter :: (F.Reify a, Row r)
        => [ColName]
        -> [ColName]
        -> SegLayout a
        -> SegAcc a
        -> r
        -> SegAcc a
segIter !keyCols !refCols !lyt !acc !row =
    let !val = constructVal keyCols lyt row
        !ref = mkCKey row refCols
    in if ref == saCurrSeg acc
       then acc { saCurrVec = (saCurrVec acc) S.|> val }
       else acc { saCurrSeg = ref
                , saSegMap  = M.insert (saCurrSeg acc)
                                       (F.ListE $ saCurrVec acc)
                                       (saSegMap acc)
                , saCurrVec = S.singleton val
                }

------------------------------------------------------------------------------
-- Construct values from table rows

mkCKey :: Row r => r -> [ColName] -> CompositeKey
mkCKey !r !cs = CompositeKey $! map (keyVal . flip col r) cs

-- | Construct a value from a vector row according to the given layout
constructVal :: Row r => [ColName] -> SegLayout a -> r -> F.Exp a
constructVal !keyCols !lyt !row =
    case lyt of
        STuple !stup      -> constructTuple keyCols stup row
        SNest _ !segMap   -> case M.lookup (mkCKey row keyCols) segMap of
                                  Just !v -> v
                                  Nothing -> F.ListE S.empty
        SCol F.DoubleT c  -> doubleVal $! (col c row)
        SCol F.IntegerT c -> integerVal $! col c row
        SCol F.BoolT c    -> boolVal $! col c row
        SCol F.CharT c    -> charVal $! col c row
        SCol F.TextT c    -> textVal $! col c row
        SCol F.UnitT c    -> unitVal $! col c row
        SCol F.DayT c     -> dayVal $! col c row
        SCol F.DecimalT c -> decimalVal $! col c row
        SCol _       _    -> $impossible

constructTuple :: Row r => [ColName] -> SegTuple a -> r -> F.Exp a
constructTuple !kc !lyt !r =
    case lyt of
        STuple2 _ !sl1 !sl2 ->
            F.TupleConstE (F.Tuple2E (constructVal kc sl1 r)
                                     (constructVal kc sl2 r))
        STuple3 _ sl1 sl2 sl3 ->
            F.TupleConstE (F.Tuple3E (constructVal kc sl1 r)
                                     (constructVal kc sl2 r)
                                     (constructVal kc sl3 r))
        STuple4 _ sl1 sl2 sl3 sl4 ->
            F.TupleConstE (F.Tuple4E (constructVal kc sl1 r)
                                     (constructVal kc sl2 r)
                                     (constructVal kc sl3 r)
                                     (constructVal kc sl4 r))
        STuple5 _ sl1 sl2 sl3 sl4 sl5 ->
            F.TupleConstE (F.Tuple5E (constructVal kc sl1 r)
                                     (constructVal kc sl2 r)
                                     (constructVal kc sl3 r)
                                     (constructVal kc sl4 r)
                                     (constructVal kc sl5 r))
        STuple6 _ sl1 sl2 sl3 sl4 sl5 sl6 ->
            F.TupleConstE (F.Tuple6E (constructVal kc sl1 r)
                                     (constructVal kc sl2 r)
                                     (constructVal kc sl3 r)
                                     (constructVal kc sl4 r)
                                     (constructVal kc sl5 r)
                                     (constructVal kc sl6 r))
        STuple7 _ sl1 sl2 sl3 sl4 sl5 sl6 sl7 ->
            F.TupleConstE (F.Tuple7E (constructVal kc sl1 r)
                                     (constructVal kc sl2 r)
                                     (constructVal kc sl3 r)
                                     (constructVal kc sl4 r)
                                     (constructVal kc sl5 r)
                                     (constructVal kc sl6 r)
                                     (constructVal kc sl7 r))
        STuple8 _ sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 ->
            F.TupleConstE (F.Tuple8E (constructVal kc sl1 r)
                                     (constructVal kc sl2 r)
                                     (constructVal kc sl3 r)
                                     (constructVal kc sl4 r)
                                     (constructVal kc sl5 r)
                                     (constructVal kc sl6 r)
                                     (constructVal kc sl7 r)
                                     (constructVal kc sl8 r))
        STuple9 _ sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 ->
            F.TupleConstE (F.Tuple9E (constructVal kc sl1 r)
                                     (constructVal kc sl2 r)
                                     (constructVal kc sl3 r)
                                     (constructVal kc sl4 r)
                                     (constructVal kc sl5 r)
                                     (constructVal kc sl6 r)
                                     (constructVal kc sl7 r)
                                     (constructVal kc sl8 r)
                                     (constructVal kc sl9 r))
        STuple10 _ sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 sl10 ->
            F.TupleConstE (F.Tuple10E (constructVal kc sl1 r)
                                      (constructVal kc sl2 r)
                                      (constructVal kc sl3 r)
                                      (constructVal kc sl4 r)
                                      (constructVal kc sl5 r)
                                      (constructVal kc sl6 r)
                                      (constructVal kc sl7 r)
                                      (constructVal kc sl8 r)
                                      (constructVal kc sl9 r)
                                      (constructVal kc sl10 r))
        STuple11 _ sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 sl10 sl11 ->
            F.TupleConstE (F.Tuple11E (constructVal kc sl1 r)
                                      (constructVal kc sl2 r)
                                      (constructVal kc sl3 r)
                                      (constructVal kc sl4 r)
                                      (constructVal kc sl5 r)
                                      (constructVal kc sl6 r)
                                      (constructVal kc sl7 r)
                                      (constructVal kc sl8 r)
                                      (constructVal kc sl9 r)
                                      (constructVal kc sl10 r)
                                      (constructVal kc sl11 r))
        STuple12 _ sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 sl10 sl11 sl12 ->
            F.TupleConstE (F.Tuple12E (constructVal kc sl1 r)
                                      (constructVal kc sl2 r)
                                      (constructVal kc sl3 r)
                                      (constructVal kc sl4 r)
                                      (constructVal kc sl5 r)
                                      (constructVal kc sl6 r)
                                      (constructVal kc sl7 r)
                                      (constructVal kc sl8 r)
                                      (constructVal kc sl9 r)
                                      (constructVal kc sl10 r)
                                      (constructVal kc sl11 r)
                                      (constructVal kc sl12 r))
        STuple13 _ sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 sl10 sl11 sl12 sl13 ->
            F.TupleConstE (F.Tuple13E (constructVal kc sl1 r)
                                      (constructVal kc sl2 r)
                                      (constructVal kc sl3 r)
                                      (constructVal kc sl4 r)
                                      (constructVal kc sl5 r)
                                      (constructVal kc sl6 r)
                                      (constructVal kc sl7 r)
                                      (constructVal kc sl8 r)
                                      (constructVal kc sl9 r)
                                      (constructVal kc sl10 r)
                                      (constructVal kc sl11 r)
                                      (constructVal kc sl12 r)
                                      (constructVal kc sl13 r))
        STuple14 _ sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 sl10 sl11 sl12 sl13 sl14 ->
            F.TupleConstE (F.Tuple14E (constructVal kc sl1 r)
                                      (constructVal kc sl2 r)
                                      (constructVal kc sl3 r)
                                      (constructVal kc sl4 r)
                                      (constructVal kc sl5 r)
                                      (constructVal kc sl6 r)
                                      (constructVal kc sl7 r)
                                      (constructVal kc sl8 r)
                                      (constructVal kc sl9 r)
                                      (constructVal kc sl10 r)
                                      (constructVal kc sl11 r)
                                      (constructVal kc sl12 r)
                                      (constructVal kc sl13 r)
                                      (constructVal kc sl14 r))
        STuple15 _ sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 sl10 sl11 sl12 sl13 sl14 sl15 ->
            F.TupleConstE (F.Tuple15E (constructVal kc sl1 r)
                                      (constructVal kc sl2 r)
                                      (constructVal kc sl3 r)
                                      (constructVal kc sl4 r)
                                      (constructVal kc sl5 r)
                                      (constructVal kc sl6 r)
                                      (constructVal kc sl7 r)
                                      (constructVal kc sl8 r)
                                      (constructVal kc sl9 r)
                                      (constructVal kc sl10 r)
                                      (constructVal kc sl11 r)
                                      (constructVal kc sl12 r)
                                      (constructVal kc sl13 r)
                                      (constructVal kc sl14 r)
                                      (constructVal kc sl15 r))
        STuple16 _ sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 sl10 sl11 sl12 sl13 sl14 sl15 sl16 ->
            F.TupleConstE (F.Tuple16E (constructVal kc sl1 r)
                                      (constructVal kc sl2 r)
                                      (constructVal kc sl3 r)
                                      (constructVal kc sl4 r)
                                      (constructVal kc sl5 r)
                                      (constructVal kc sl6 r)
                                      (constructVal kc sl7 r)
                                      (constructVal kc sl8 r)
                                      (constructVal kc sl9 r)
                                      (constructVal kc sl10 r)
                                      (constructVal kc sl11 r)
                                      (constructVal kc sl12 r)
                                      (constructVal kc sl13 r)
                                      (constructVal kc sl14 r)
                                      (constructVal kc sl15 r)
                                      (constructVal kc sl16 r))

--------------------------------------------------------------------------------
