{-# LANGUAGE ScopedTypeVariables #-}
module Database.DSH.ExecuteFlattening where

import qualified Language.ParallelLang.DBPH as P
import Database.DSH.Data
import Database.HDBC
import Control.Exception (evaluate)
import Database.DSH.Data
import Data.Convertible

import Data.Maybe (fromJust)

data SQL a = SQL (P.Query P.SQL)

executeQuery :: forall a. forall conn. (QA a, IConnection conn) => conn -> SQL a -> IO a
executeQuery c (SQL (P.PrimVal (P.SQL _ s q))) = do
                                                    (r, d) <- doQuery c q
                                                    let (iC, ri) = schemeToResult s d
                                                    let parted = partByIter iC r
                                                    let i = snd (fromJust ri)
                                                    let t = reify (undefined :: a)
                                                    return $ fromNorm $ snd $ head $ normalise t i parted 
                                                    
normalise :: Type -> Int -> [(Int, [(Int, [SqlValue])])] -> [(Int, Norm)]
normalise IntegerT i [(_, [(_, v)])] = [(1, convert (v !! i, IntegerT))]
normalise _        _ _ = undefined
                                                    
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
                          in (i, (p, v):vi) : pbi vs
        pbi []         = []
        getIter :: [SqlValue] -> Int
        getIter vals = ((fromSql (vals !! iC))::Int)
        
type ResultInfo = (Int, Maybe (String, Int))

-- | Transform algebraic plan scheme info into resultinfo
schemeToResult :: P.Schema -> [(String, SqlColDesc)] -> ResultInfo
schemeToResult (itN, col) resDescr = let resColumns = flip zip [0..] $ map (\(c, _) -> takeWhile (\a -> a /= '_') c) resDescr
                                         itC = fromJust $ lookup itN resColumns
                                      in (itC, fmap (\(n, _) -> (n, fromJust $ lookup n resColumns)) col)