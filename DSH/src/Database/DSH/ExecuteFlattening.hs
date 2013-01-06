{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TransformListComp     #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Database.DSH.ExecuteFlattening(executeSQLQuery, executeX100Query, SQL(..), X100(..)) where

import           Database.DSH.Impossible
import           Database.DSH.Internals

import           Database.X100Client                   hiding (X100)

import           Database.HDBC

import           Control.Exception                     (evaluate)

import           GHC.Exts

import           Data.Convertible.Base
import           Data.List                             (foldl', transpose)
import           Data.Maybe                            (fromJust)
import           Data.Text                             (Text(), pack)
import qualified Data.Text                             as Txt
import qualified Data.Text.Encoding                    as Txt

import qualified Database.DSH.Flattening.VL.Data.Query as Q

data SQL a = SQL (Q.Query Q.SQL)

data X100 a = X100 (Q.Query Q.X100)

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

executeX100Query :: forall a. (Reify a) => X100Info -> X100 a -> IO (Exp a)
executeX100Query c (X100 q) = let et = reify (undefined :: a)
                                  in case et of
                                        (ListT _) -> do
                                                      n <- makeNormX100 c q et
                                                      return $ concatN $ reverse $ map snd n
                                        _ -> do
                                                n <- makeNormX100Prim c q et
                                                return n

constructVector :: X100Info -> Q.Layout Q.X100 -> [(Int, [(Int, [X100Data])])] -> Type [a] -> IO [(Int, Exp [a])]
constructVector _ (Q.InColumn i) parted t = do
                                            return $ normaliseX100List t i parted
constructVector c (Q.Nest v lyt) parted t@(ListT _) =
                                        case t of
                                            (ListT t1@(ListT _)) -> do
                                                            inner <- makeNormX100 c (Q.ValueVector v lyt) t1
                                                            return $ constructDescriptor t (map (\(i, p) -> (i, map fst p)) parted) inner
                                            _ -> error "constructVector: Not a nested list"
constructVector c (Q.Pair p1 p2) parted (ListT (PairT t1 t2)) = do
                                                                    v1 <- constructVector c p1 parted $ ListT t1
                                                                    v2 <- constructVector c p2 parted $ ListT t2
                                                                    return $ makeTuple v1 v2
constructVector _ v _ t = error $ "result " ++ show v ++ " with type: " ++ show t

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

makeNormX100 :: X100Info -> Q.Query Q.X100 -> Type [a] -> IO [(Int, Exp [a])]
makeNormX100 c (Q.ValueVector (Q.X100 _ q) p) t = do
                                                   (X100Res _ res) <- doX100Query c q
                                                   let parted = partByIterX100 res
                                                   constructVector c p parted t
makeNormX100 _ _ _ = error "makeNormX100: Not a list value vector"

makeNormX100Prim :: (Reify a) => X100Info -> Q.Query Q.X100 -> Type a -> IO (Exp a)
makeNormX100Prim c (Q.PrimVal (Q.X100 _ q) p) t = do
                                        (X100Res _ res) <- doX100Query c q
                                        let parted = partByIterX100 res
                                        [(_, (ListE [n]))] <- constructVector c p parted (ListT t)
                                        return n
makeNormX100Prim _ _ _ = error "makeNormX100Prim: Not a primitive value query"

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

normaliseX100List :: Type [a] -> Int -> [(Int, [(Int, [X100Data])])] -> [(Int, Exp [a])]
normaliseX100List (ListT t1) index vs = reverse $ foldl' (\tl (i, v) -> (i, ListE (map ((normaliseX100 t1) . (!! (index - 1)) . snd) v)):tl) [] vs

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

normaliseX100 :: Type a -> X100Data -> Exp a
normaliseX100 UnitT _ = UnitE
normaliseX100 t v = convert (v, t)

instance Convertible (X100Data, Type a) (Exp a) where
    safeConvert (Str s, TextT) = Right $ TextE (pack s)
    safeConvert (Str s, CharT) = Right $ CharE (head s)
    safeConvert (UChr i, BoolT) = Right $ BoolE (i /= 0)
    safeConvert (SChr i, BoolT) = Right $ BoolE (i /= 0)
    safeConvert (SInt i, BoolT) = Right $ BoolE (i /= 0)
    safeConvert (UInt i, BoolT) = Right $ BoolE (i /= 0)
    safeConvert (SSht i, BoolT) = Right $ BoolE (i /= 0)
    safeConvert (USht i, BoolT) = Right $ BoolE (i /= 0)
    safeConvert (SLng i, BoolT) = Right $ BoolE (i /= 0)
    safeConvert (ULng i, BoolT) = Right $ BoolE (i /= 0)
    safeConvert (UIDX i, BoolT) = Right $ BoolE (i /= 0)
    safeConvert (SInt i, IntegerT) = Right $ IntegerE (toInteger i)
    safeConvert (UInt i, IntegerT) = Right $ IntegerE (toInteger i)
    safeConvert (SChr i, IntegerT) = Right $ IntegerE (toInteger i)
    safeConvert (UChr i, IntegerT) = Right $ IntegerE (toInteger i)
    safeConvert (SSht i, IntegerT) = Right $ IntegerE (toInteger i)
    safeConvert (USht i, IntegerT) = Right $ IntegerE (toInteger i)
    safeConvert (SLng i, IntegerT) = Right $ IntegerE i
    safeConvert (ULng i, IntegerT) = Right $ IntegerE i
    safeConvert (UIDX i, IntegerT) = Right $ IntegerE i
    safeConvert (Dbl d, DoubleT) = Right $ DoubleE d
    safeConvert _                = error $ "cannot convert (X100Data, Type) to Norm"

doSQLQuery :: IConnection conn => conn -> String -> IO ([[SqlValue]], [(String, SqlColDesc)])
doSQLQuery c q = do
                sth <- prepare c q
                _ <- execute sth []
                res <- dshFetchAllRowsStrict sth
                resDescr <- describeResult sth
                return (res, resDescr)

doX100Query :: X100Info -> String -> IO X100Result
doX100Query c q = executeQuery c q

dshFetchAllRowsStrict :: Statement -> IO [[SqlValue]]
dshFetchAllRowsStrict stmt = go []
  where
  go :: [[SqlValue]] -> IO [[SqlValue]]
  go acc = do  mRow <- fetchRow stmt
               case mRow of
                 Nothing   -> return (reverse acc)
                 Just row  -> do mapM_ evaluate row
                                 go (row : acc)

partByIterX100 :: [X100Column] -> [(Int, [(Int, [X100Data])])]
partByIterX100 d = pbi d'
    where
        d' :: [(Int, Int, [X100Data])]
        d' = case d of
                [descr, p] -> zipWith (\x y -> (x, y, [])) (map convert descr) (map convert p)
                (descr:(p:vs)) -> zip3 (map convert descr) (map convert p) $ transpose vs
                _          -> $impossible
        pbi :: [(Int, Int, [X100Data])] -> [(Int, [(Int, [X100Data])])]
        pbi vs = [ (the i, zip p it) | (i, p, it) <- vs
                                     , then group by i using groupWith]

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

