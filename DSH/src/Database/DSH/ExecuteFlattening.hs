{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TransformListComp     #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Database.DSH.ExecuteFlattening(executeSQLQuery, executeX100Query, SQL(..), X100(..)) where

import           Database.DSH.Impossible
import           Database.DSH.Internals

import           Database.HDBC

import           Control.Exception                     (evaluate)
import           Control.Monad

import           GHC.Exts

import           Data.Convertible.Base
import           Data.List                             (foldl', transpose)
import           Data.Maybe                            (fromJust)
import           Data.Text                             (Text(), pack)
import qualified Data.Text                             as Txt
import qualified Data.Text.Encoding                    as Txt
import           Text.Printf

import           Database.DSH.Common.Data.DBCode
import           Database.DSH.Common.Data.QueryPlan

import qualified Data.Map as M
import qualified Data.IntMap.Strict as IM
import qualified Data.DList as D


itemCol :: Int -> String
itemCol 1 = "item1"
itemCol 2 = "item2"
itemCol 3 = "item3"
itemCol 4 = "item4"
itemCol 5 = "item5"
itemCol 6 = "item6"
itemCol 7 = "item7"
itemCol 8 = "item8"
itemCol 9 = "item9"
itemCol 10 = "item10"
itemCol n = "item" ++ show n

type SqlRow = M.Map String SqlValue
type SqlTable = [SqlRow]

col :: String -> SqlRow -> SqlValue
col c r = 
    case M.lookup c r of
        Just v  -> v
        Nothing -> $impossible

int32 :: SqlValue -> Int
int32 (SqlInt32 i) = fromIntegral i
int32 _            = $impossible

posCol :: SqlRow -> Int
posCol row = int32 $ col "pos" row

descrCol :: SqlRow -> Int
descrCol row = int32 $ col "descr" row

data TabLayout a = TCol (Type a) String
                 | TNest (Type [a]) SqlTable (TabLayout a)
                 | TPair (Type (a, b)) (TabLayout a) (TabLayout b)

-- | Traverse the layout and execute all subqueries for nested vectors
execAll :: IConnection conn => conn -> TopLayout SQLCode -> Type a -> IO (TabLayout a)
execAll conn lyt ty =
    case (lyt, ty) of
        (InColumn i, t)               -> return $ TCol t (itemCol i)
        (Pair lyt1 lyt2, PairT t1 t2) -> do
            lyt1' <- execAll conn lyt1 t1
            lyt2' <- execAll conn lyt2 t2
            return $ TPair ty lyt1' lyt2'
        (Nest sqlQuery clyt, ListT t) -> do
            stmt  <- prepare conn sqlQuery
            tab   <- fetchAllRowsMap' stmt
            clyt' <- execAll conn clyt t
            return $ TNest ty tab clyt'
        (_, _) -> error "Type does not match query structure"

type SegMap a = IM.IntMap (Exp a)

data SegLayout a = SCol (Type a) String
                 | SNest (SegMap a)
                 | SPair (SegLayout a) (SegLayout a)

-- | Construct values for nested vectors in the layout.
segmentLayout :: TabLayout a -> SegLayout a
segmentLayout tlyt =
    case tlyt of
        TCol t s          -> SCol t s
        TNest tab clyt    -> SNest (fromSegVector tab clyt)
        TPair clyt1 clyt2 -> SPair (segmentLayout clyt1) (segmentLayout clyt2)

data SegAcc a = SegAcc { currSeg :: Int
                       , segMap  :: SegMap [a]
                       , currVec :: D.DList (Exp a)
                       }

fromSegVector :: SqlTable -> TabLayout a -> SegMap [a]
fromSegVector tab tlyt =
    let slyt = segmentLayout tlyt
        initialAcc = SegAcc { currSeg = 0, segMap = IM.empty, currVec = D.empty }
        finalAcc = foldl' (segIter slyt) initialAcc tab
    in IM.insert (currSeg finalAcc) (ListE $ D.toList $ currVec finalAcc) (segMap finalAcc)

-- Fold iterator that constructs a map from segment descriptor to the
-- list value that is represented by that segment
segIter :: SegLayout a -> SegAcc [a] -> SqlRow -> SegAcc [a]
segIter lyt acc row = 
    let val   = mkVal lyt row
        descr = descrCol row
    in if descr == currSeg acc
       then acc { currVec = D.snoc (currVec acc) val }
       else acc { currSeg = descr
                , segMap  = IM.insert (currSeg acc) (ListE $ D.toList $ currVec acc) (segMap acc)
                , currVec = D.singleton val
                }

-- | Construct a value from a vector row according to the given layout
mkVal :: SegLayout a -> SqlRow -> Exp a
mkVal lyt row =
    case lyt of
        SPair lyt1 lyt2 -> PairE (mkVal lyt1 row) (mkVal lyt2 row)
        SNest segmap    -> let pos = posCol row
                           in case IM.lookup pos segmap of
                                  Just v  -> v
                                  Nothing -> ListE []
        SCol t c        -> scalarFromSql (col c row) t 

scalarFromSql :: SqlValue -> Type a -> Exp a
scalarFromSql SqlNull         UnitT    = UnitE
scalarFromSql (SqlInteger i)  IntegerT = IntegerE i
scalarFromSql (SqlInt32 i)    IntegerT = IntegerE $ fromIntegral i
scalarFromSql (SqlInt64 i)    IntegerT = IntegerE $ fromIntegral i
scalarFromSql (SqlWord32 i)   IntegerT = IntegerE $ fromIntegral i
scalarFromSql (SqlWord64 i)   IntegerT = IntegerE $ fromIntegral i
scalarFromSql (SqlDouble d)  DoubleT    = DoubleE d
scalarFromSql (SqlRational d) DoubleT = DoubleE $ fromRational d
scalarFromSql (SqlInteger d)  DoubleT = DoubleE $ fromIntegral d
scalarFromSql (SqlInt32 d)    DoubleT = DoubleE $ fromIntegral d
scalarFromSql (SqlInt64 d)    DoubleT = DoubleE $ fromIntegral d
scalarFromSql (SqlWord32 d)   DoubleT = DoubleE $ fromIntegral d
scalarFromSql (SqlWord64 d)   DoubleT = DoubleE $ fromIntegral d
scalarFromSql (SqlBool b) BoolT       = BoolE b
scalarFromSql (SqlInteger i) BoolT    = BoolE (i /= 0)
scalarFromSql (SqlInt32 i)   BoolT    = BoolE (i /= 0)
scalarFromSql (SqlInt64 i)   BoolT    = BoolE (i /= 0)
scalarFromSql (SqlWord32 i)  BoolT    = BoolE (i /= 0)
scalarFromSql (SqlWord64 i)  BoolT    = BoolE (i /= 0)
scalarFromSql (SqlChar c) CharT       = CharE c
scalarFromSql (SqlString (c:_)) CharT = CharE c
scalarFromSql (SqlByteString c) CharT = CharE (head $ Txt.unpack $ Txt.decodeUtf8 c)
scalarFromSql (SqlString t) TextT     = TextE (Txt.pack t)
scalarFromSql (SqlByteString s) TextT = TextE (Txt.decodeUtf8 s)
scalarFromSql sql                 _   = error $ "Unsupported SqlValue: "  ++ show sql

