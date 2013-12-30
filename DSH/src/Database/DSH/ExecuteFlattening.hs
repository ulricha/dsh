{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TransformListComp     #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Database.DSH.ExecuteFlattening(executeSQLQuery, SQL(..)) where

import           Database.DSH.Impossible
import           Database.DSH.Internals

import           Database.HDBC

import           Control.Exception                     (evaluate)

import           GHC.Exts

import           Data.Convertible.Base
import           Data.List                             (foldl', transpose)
import           Data.Maybe                            (fromJust)
import           Data.Text                             (Text(), pack)
import qualified Data.Text                             as Txt
import qualified Data.Text.Encoding                    as Txt
import           Text.Printf

import qualified Database.DSH.VL.Data.Query as Q

data SQL a = SQL (Q.Query Q.SQL)

textToChar :: Exp Text -> Exp Char
textToChar (TextE t) = CharE (Txt.head t)
textToChar _               = error $ "textToChar: Not a char value"

executeSQLQuery :: forall a. forall conn. (IConnection conn, Reify a) => conn -> SQL a -> IO (Exp a)
executeSQLQuery c (SQL q) = let et = reify (undefined :: a)
                             in case et of
                                 (ListT _) -> do
                                                n <- makeNormSQL c q et
                                                return $ concatN $ reverse $ map snd n
                                 _         -> do
                                                n <- makeNormSQLPrim c q et
                                                return $ n

constructVectorSQL :: IConnection conn => conn -> Q.Layout Q.SQL -> [(String, Int)] -> [(Int, [(Int, [SqlValue])])] -> Type [a] -> IO [(Int, Exp [a])]
constructVectorSQL _ (Q.InColumn i) pos parted t = do
                                            let i' = snd $ pos !! (i - 1)
                                            return $ normaliseList t i' parted
constructVectorSQL c (Q.Nest v lyt) _ parted t@(ListT _) =
                                        case t of
                                          (ListT t1@(ListT _)) -> do
                                                            inner <- makeNormSQL c (Q.ValueVector v lyt) t1
                                                            return $ constructDescriptor t (map (\(i, p) -> (i, map fst p)) parted) inner
                                          _ -> error "constructVectorSQL: Not a nested list"
constructVectorSQL c (Q.Pair p1 p2) pos parted (ListT (PairT t1 t2)) = do
                                                                    v1 <- constructVectorSQL c p1 pos parted $ ListT t1
                                                                    v2 <- constructVectorSQL c p2 pos parted $ ListT t2
                                                                    return $ makeTuple v1 v2
constructVectorSQL _ _ _ _ _ = $impossible

makeTuple :: [(Int, Exp [a])] -> [(Int, Exp [b])] -> [(Int, Exp [(a, b)])]
makeTuple ((i1, vs1):v1) ((i2, vs2):v2) | i1 == i2  = (i1, zipNorm vs1 vs2) : makeTuple v1 v2
                                        | otherwise = error "makeTuple: Cannot zip"
makeTuple []             []                         = []
makeTuple _              _                          = $impossible

zipNorm :: Exp [a] -> Exp [b] -> Exp [(a, b)]
zipNorm (ListE es1) (ListE es2) = ListE [PairE e1 e2 | (e1, e2) <- zip es1 es2]
zipNorm _ _ = error "zipNorm: Cannot zip"

makeNormSQLPrim :: (IConnection conn, Reify a) => conn -> Q.Query Q.SQL -> Type a -> IO (Exp a)
makeNormSQLPrim c (Q.PrimVal (Q.SQL _ s q) p) t = do
                                        (r, d) <- doSQLQuery c q
                                        let (iC, ri) = schemeToResult s d
                                        let parted = partByIter iC r
                                        [(_, (ListE [n]))] <- constructVectorSQL c p ri parted (ListT t)
                                        return n
makeNormSQLPrim _ _ _ = error "makeNormSQLPrim: Not a primitive value query"

makeNormSQL :: IConnection conn => conn -> Q.Query Q.SQL -> Type [a] -> IO [(Int, Exp [a])]
makeNormSQL c (Q.ValueVector (Q.SQL _ s q) p) t = do
                                                    (r, d) <- doSQLQuery c q
                                                    let (iC, ri) = schemeToResult s d
                                                    let parted = partByIter iC r
                                                    constructVectorSQL c p ri parted t
makeNormSQL _ _ _ = error "makeNormSQL: Not a value vector"

constructDescriptor :: Reify a => Type [[a]] -> [(Int, [Int])] -> [(Int, Exp [a])] -> [(Int, Exp [[a]])]
constructDescriptor t@(ListT t1) ((i, vs):outers) inners = let (r, inners') = nestList t1 vs inners
                                                            in (i, ListE r) : constructDescriptor t outers inners'
constructDescriptor _            []               _      = []

nestList :: Reify a => Type [a] -> [Int] -> [(Int, Exp [a])] -> ([Exp [a]], [(Int, Exp [a])])
nestList t ps'@(p:ps) ls@((d,n):lists) | p == d = n `combine` (nestList t ps lists)
                                       | p <  d = ListE [] `combine` (nestList t ps ls)
                                       | p >  d = nestList t ps' lists
nestList t (_:ps)     []                         = ListE [] `combine` (nestList t ps [])
nestList _ []         ls                         = ([], ls)
nestList _ _ _ = error "nestList $ Not a neted list"

combine :: Exp [a] -> ([Exp [a]], [(Int, Exp [a])]) -> ([Exp [a]], [(Int, Exp [a])])
combine n (ns, r) = (n:ns, r)

concatN :: Reify a => [Exp [a]] -> Exp [a]
concatN ns@((ListE _): _) = foldl' (\(ListE e1) (ListE e2) -> ListE (e2 ++ e1)) (ListE []) ns
concatN []                = ListE []
concatN _                 = error "concatN: Not a list of lists"

normaliseList :: Type [a] -> Int -> [(Int, [(Int, [SqlValue])])] -> [(Int, Exp [a])]
normaliseList (ListT t1) c vs = reverse $ foldl' (\tl (i, v) -> (i, ListE (map ((normalise t1 c) . snd) v)):tl) [] vs

normalise :: Type a -> Int -> [SqlValue] -> Exp a
normalise UnitT _ _ = UnitE
normalise t i v = convert' (v !! i) t

convert' :: SqlValue -> Type a -> Exp a
convert' SqlNull         UnitT    = UnitE
convert' (SqlInteger i)  IntegerT = IntegerE i
convert' (SqlInt32 i)    IntegerT = IntegerE $ fromIntegral i
convert' (SqlInt64 i)    IntegerT = IntegerE $ fromIntegral i
convert' (SqlWord32 i)   IntegerT = IntegerE $ fromIntegral i
convert' (SqlWord64 i)   IntegerT = IntegerE $ fromIntegral i
convert' (SqlDouble d)  DoubleT  = DoubleE d
convert' (SqlRational d) DoubleT = DoubleE $ fromRational d
convert' (SqlInteger d)  DoubleT = DoubleE $ fromIntegral d
convert' (SqlInt32 d)    DoubleT = DoubleE $ fromIntegral d
convert' (SqlInt64 d)    DoubleT = DoubleE $ fromIntegral d
convert' (SqlWord32 d)   DoubleT = DoubleE $ fromIntegral d
convert' (SqlWord64 d)   DoubleT = DoubleE $ fromIntegral d
convert' (SqlBool b) BoolT       = BoolE b
convert' (SqlInteger i) BoolT    = BoolE (i /= 0)
convert' (SqlInt32 i)   BoolT    = BoolE (i /= 0)
convert' (SqlInt64 i)   BoolT    = BoolE (i /= 0)
convert' (SqlWord32 i)  BoolT    = BoolE (i /= 0)
convert' (SqlWord64 i)  BoolT    = BoolE (i /= 0)
convert' (SqlChar c) CharT       = CharE c
convert' (SqlString (c:_)) CharT = CharE c
convert' (SqlByteString c) CharT = CharE (head $ Txt.unpack $ Txt.decodeUtf8 c)
convert' (SqlString t) TextT     = TextE (Txt.pack t)
convert' (SqlByteString s) TextT = TextE (Txt.decodeUtf8 s)
convert' sql                 _   = error $ "Unsupported SqlValue: "  ++ show sql

doSQLQuery :: IConnection conn => conn -> String -> IO ([[SqlValue]], [(String, SqlColDesc)])
doSQLQuery c q = do
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
partByIter iC vals = pbi (zip [1..] vals)
    where
        pbi :: [(Int, [SqlValue])] -> [(Int, [(Int, [SqlValue])])]
        pbi ((p,v):vs) = let i = getIter v
                             (vi, vr) = span (\v' -> i == (getIter $ snd v')) vs
                          in (i, (p, v):vi) : pbi vr
        pbi []         = []
        getIter :: [SqlValue] -> Int
        getIter vs = ((fromSql (vs !! iC))::Int)

type ResultInfo = (Int, [(String, Int)])

-- | Transform algebraic plan scheme info into resultinfo
schemeToResult :: Q.Schema -> [(String, SqlColDesc)] -> ResultInfo
schemeToResult (itN, col) resDescr = let resColumns = flip zip [0..] $ map (\(c, _) -> takeWhile (\a -> a /= '_') c) resDescr
                                         itC = fromJust $ lookup itN resColumns
                                      in (itC, map (\(n, _) -> (n, fromJust $ lookup n resColumns)) col)

