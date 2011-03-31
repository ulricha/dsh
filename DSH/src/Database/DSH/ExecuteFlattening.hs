{-# LANGUAGE ScopedTypeVariables #-}
module Database.DSH.ExecuteFlattening where

import qualified Language.ParallelLang.DBPH as P
import Database.DSH.Data
import Database.HDBC
import Control.Exception (evaluate)
import Database.DSH.Data
import Data.Convertible

import Data.List (foldl')

import Data.Maybe (fromJust)

data SQL a = SQL (P.Query P.SQL)

executeQuery :: forall a. forall conn. (QA a, IConnection conn) => conn -> SQL a -> IO a
executeQuery c (SQL (P.PrimVal (P.SQL _ s q))) = do
                                                    (r, d) <- doQuery c q
                                                    let (iC, ri) = schemeToResult s d
                                                    let [(_, [(_, v)])] = partByIter iC r
                                                    let i = snd (fromJust ri)
                                                    let t = reify (undefined :: a)
                                                    return $ fromNorm $ normalise t i v
executeQuery c (SQL (P.ValueVector (P.SQL _ s q))) = do
                                                      (r, d) <- doQuery c q
                                                      let (iC, ri) = schemeToResult s d
                                                      let parted = partByIter iC r
                                                      let i = snd (fromJust ri)
                                                      let t = reify (undefined :: a)
                                                      return $ fromNorm $ concatN $ map snd $ normaliseList t i parted

concatN :: [Norm] -> Norm
concatN ns@((ListN ls t1):_) = foldl' (\(ListN e t) (ListN e1 _) -> ListN (e1 ++ e) t) (ListN [] t1) ns
concatN _                    = error "concatN: Not a list of lists"

normaliseList :: Type -> Int -> [(Int, [(Int, [SqlValue])])] -> [(Int, Norm)]
normaliseList t@(ListT t1) c vs = foldl' (\tl (i, v) -> (i, ListN (map ((normalise t1 c) . snd) v) t):tl) [] vs
normaliseList _            _ _  = error "normaliseList: Should not happen"

normalise :: Type -> Int -> [SqlValue] -> Norm
normalise t i v = convert (v !! i, t)
                                                    
doQuery :: IConnection conn => conn -> String -> IO ([[SqlValue]], [(String, SqlColDesc)])
doQuery c q = do
                sth <- prepare c q
                _ <- execute sth []
                res <- dshFetchAllRowsStrict sth
                resDescr <- describeResult sth
                return (res, resDescr)
                
                
dshFetchAllRowsStrict :: Statement -> IO [[SqlValue]]
dshFetchAllRowsStrict stmt = go []
  where
  go :: [[SqlValue]] -> IO [[SqlValue]]
  go acc = do  mRow <- fetchRow stmt
               case mRow of
                 Nothing   -> return (reverse acc)
                 Just row  -> do mapM_ evaluate row
                                 go (row : acc)
                                 
partByIter :: Int -> [[SqlValue]] -> [(Int, [(Int, [SqlValue])])]
partByIter iC vs = pbi (zip [1..] vs)
    where
        pbi :: [(Int, [SqlValue])] -> [(Int, [(Int, [SqlValue])])]
        pbi ((p,v):vs) = let i = getIter v
                             (vi, vr) = span (\(p',v') -> i == getIter v') vs
                          in (i, (p, v):vi) : pbi vr
        pbi []         = []
        getIter :: [SqlValue] -> Int
        getIter vals = ((fromSql (vals !! iC))::Int)
        
type ResultInfo = (Int, Maybe (String, Int))

-- | Transform algebraic plan scheme info into resultinfo
schemeToResult :: P.Schema -> [(String, SqlColDesc)] -> ResultInfo
schemeToResult (itN, col) resDescr = let resColumns = flip zip [0..] $ map (\(c, _) -> takeWhile (\a -> a /= '_') c) resDescr
                                         itC = fromJust $ lookup itN resColumns
                                      in (itC, fmap (\(n, _) -> (n, fromJust $ lookup n resColumns)) col)