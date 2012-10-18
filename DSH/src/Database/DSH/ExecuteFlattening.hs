{-# LANGUAGE ScopedTypeVariables, TemplateHaskell, ParallelListComp, TransformListComp, FlexibleInstances, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Database.DSH.ExecuteFlattening(executeSQLQuery, executeX100Query, SQL(..), X100(..)) where

import qualified Language.ParallelLang.DBPH as P
import qualified Language.ParallelLang.Common.Data.Type as T

import Database.DSH.Internals
import Database.DSH.Impossible

import Database.X100Client hiding (X100)

import Database.HDBC

import Control.Exception (evaluate)
import Control.Monad(liftM)

import GHC.Exts

import Data.Convertible
import Data.Text (pack)
import qualified Data.Text as Txt
import Data.List (foldl', transpose)
import Data.Maybe (fromJust)

import Control.Applicative

data SQL a = SQL (P.Query P.SQL)

data X100 a = X100 (P.Query P.X100)

fromFType :: T.Type -> Type
fromFType (T.Var _) = $impossible
fromFType (T.Fn _ _)  = $impossible
fromFType (T.Int)   = IntegerT
fromFType (T.Bool)  = BoolT
fromFType (T.Double) = DoubleT
fromFType (T.String) = TextT
fromFType (T.Unit) = UnitT
fromFType (T.Nat) = IntegerT
fromFType (T.Pair e1 e2) = TupleT (fromFType e1) (fromFType e2)
fromFType (T.List t) = ListT (fromFType t)

typeReconstructor :: Type -> Type -> (Type, Norm -> Norm)
typeReconstructor o ex | o == ex = (o, id)
                       | o == TextT && ex == CharT = (ex, textToChar)
                       | otherwise = case ex of
                                        ListT _ -> let (t1, f1) = pushIn ex
                                                       (t2, f2) = typeReconstructor o t1
                                                    in (t2, f1 . f2)
                                        TupleT t1 t2 -> case o of
                                                         TupleT to1 to2 -> let r1@(t1',_) = typeReconstructor to1 t1
                                                                               r2@(t2',_) = typeReconstructor to2 t2
                                                                            in (TupleT t1' t2', onPair r1 r2)
                                                         _ -> error "cannot reconstruct type"
                                        CharT -> (CharT, textToChar)
                                        t -> error $ "This type cannot be reconstructed: " ++ show t ++ " provided: " ++ show o

textToChar :: Norm -> Norm
textToChar (TextN t TextT) = CharN (Txt.head t) CharT
textToChar _               = error $ "textToChar: Not a char value"

onPair :: (Type, Norm -> Norm) -> (Type, Norm -> Norm) -> Norm -> Norm
onPair (t1, f1) (t2, f2) (TupleN e1 e2 _) = TupleN (f1 e1) (f2 e2) (TupleT t1 t2)
onPair _ _ _ = error "onPair: Not a pair value"
                                                         
pushIn :: Type -> (Type, Norm -> Norm)
pushIn (ListT (TupleT e1 e2)) = (TupleT (ListT e1) (ListT e2), zipN)
pushIn ty@(ListT v@(ListT _)) = let (t, f) = pushIn v
                                 in (ListT t, mapN (ty, f))
pushIn t = (t, id)
                      
mapN :: (Type, Norm -> Norm) -> Norm -> Norm
mapN (t, f) (ListN es _) = ListN (map f es) t
mapN (t, _) v = error $ "This can't be: " ++ show t ++ "\n" ++ show v
                                      
retuple :: Type -> Type -> Norm -> Norm
retuple t te v = let (_, f) = typeReconstructor t te
                  in f v

zipN :: Norm -> Norm
zipN (TupleN (ListN es1 (ListT t1)) (ListN es2 (ListT t2)) _) = ListN [TupleN e1 e2 (TupleT t1 t2) | e1 <- es1 | e2 <- es2] (ListT (TupleT t1 t2))
zipN e = error $ "zipN: " ++ show e -- $impossible

executeSQLQuery :: forall a. forall conn. (QA a, IConnection conn) => conn -> T.Type -> SQL a -> IO a
executeSQLQuery c vt (SQL q) = do
                                let et = reify (undefined :: a)
                                let gt = fromFType vt
                                n <- makeNormSQL c q (fromFType vt)
                                return $ fromNorm $ retuple gt et $ fromEither (fromFType vt) n

executeX100Query :: forall a. QA a => X100Info -> T.Type -> X100 a -> IO a
executeX100Query c vt (X100 q) = do
                                  let et = reify (undefined :: a)
                                  let gt = fromFType vt
                                  n <- makeNormX100 c q (fromFType vt)
                                  return $ fromNorm $ retuple gt et $ fromEither (fromFType vt) n

constructVector :: X100Info -> P.Layout P.X100 -> [(Int, [(Int, [X100Data])])] -> Type -> IO [(Int, Norm)]
constructVector _ (P.InColumn i) parted t = do
                                            return $ normaliseX100List t i parted
constructVector c (P.Nest v lyt) parted t@(ListT t1) = do
                                        inner <- liftM fromRight $ makeNormX100 c (P.ValueVector v lyt) t1
                                        return $ constructDescriptor t (map (\(i, p) -> (i, map fst p)) parted) inner
constructVector c (P.Pair p1 p2) parted (ListT (TupleT t1 t2)) = do
                                                                    v1 <- constructVector c p1 parted $ ListT t1
                                                                    v2 <- constructVector c p2 parted $ ListT t2
                                                                    return $ makeTuple v1 v2
constructVector _ v _ t = error $ "result " ++ show v ++ " with type: " ++ show t
-- constructVector _ _ _ _ = $impossible
                                             
constructVectorSQL :: IConnection conn => conn -> P.Layout P.SQL -> [(String, Int)] -> [(Int, [(Int, [SqlValue])])] -> Type -> IO [(Int, Norm)]
constructVectorSQL _ (P.InColumn i) pos parted t = do
                                            let i' = snd $ pos !! (i - 1)
                                            return $ normaliseList t i' parted
constructVectorSQL c (P.Nest v lyt) _ parted t@(ListT t1) = do
                                        inner <- liftM fromRight $ makeNormSQL c (P.ValueVector v lyt) t1
                                        return $ constructDescriptor t (map (\(i, p) -> (i, map fst p)) parted) inner
constructVectorSQL c (P.Pair p1 p2) pos parted (ListT (TupleT t1 t2)) = do
                                                                    v1 <- constructVectorSQL c p1 pos parted $ ListT t1
                                                                    v2 <- constructVectorSQL c p2 pos parted $ ListT t2
                                                                    return $ makeTuple v1 v2
constructVectorSQL _ _ _ _ _ = $impossible


makeTuple :: [(Int, Norm)] -> [(Int, Norm)] -> [(Int, Norm)]
makeTuple ((i1, vs1):v1) ((i2, vs2):v2) | i1 == i2  = (i1, zipNorm vs1 vs2) : makeTuple v1 v2
                                        | otherwise = error "makeTuple: Cannot zip"
makeTuple []             []                         = []
makeTuple _              _                          = $impossible

zipNorm :: Norm -> Norm -> Norm
zipNorm (ListN es1 (ListT t1)) (ListN es2 (ListT t2)) = ListN [TupleN e1 e2 (TupleT t1 t2) | (e1, e2) <- zip es1 es2] (ListT $ TupleT t1 t2)
zipNorm _ _ = error "zipNorm: Cannot zip"

makeNormX100 :: X100Info -> P.Query P.X100 -> Type -> IO (Either Norm [(Int, Norm)])
makeNormX100 c (P.ValueVector (P.X100 _ q) p) t = do
                                                   (X100Res _ res) <- doX100Query c q
                                                   let parted = partByIterX100 res
                                                   Right <$> constructVector c p parted t
makeNormX100 c (P.PrimVal (P.X100 _ q) p) t = do
                                              (X100Res _ res) <- doX100Query c q
                                              let parted = partByIterX100 res
                                              [(_, (ListN [n] _))] <- constructVector c p parted (ListT t)
                                              return $ Left n

makeNormSQL :: IConnection conn => conn -> P.Query P.SQL -> Type -> IO (Either Norm [(Int, Norm)])
makeNormSQL c (P.ValueVector (P.SQL _ s q) p) t = do
                                                    (r, d) <- doSQLQuery c q
                                                    let (iC, ri) = schemeToResult s d
                                                    let parted = partByIter iC r
                                                    Right <$> constructVectorSQL c p ri parted t
makeNormSQL c (P.PrimVal (P.SQL _ s q) p) t = do
                                                (r, d) <- doSQLQuery c q
                                                let (iC, ri) = schemeToResult s d
                                                let parted = partByIter iC r
                                                [(_, (ListN [n] _))] <- constructVectorSQL c p ri parted (ListT t)
                                                return $ Left n

fromRight :: Either a b -> b
fromRight (Right x) = x
fromRight _         = error "fromRight"

fromEither :: Type -> Either Norm [(Int, Norm)] -> Norm
fromEither _ (Left n) = n
fromEither t (Right ns) = concatN t $ reverse $ map snd ns

constructDescriptor :: Type -> [(Int, [Int])] -> [(Int, Norm)] -> [(Int, Norm)]
constructDescriptor t@(ListT t1) ((i, vs):outers) inners = let (r, inners') = nestList t1 vs inners
                                                            in (i, ListN r t) : constructDescriptor t outers inners'
constructDescriptor _            []               _      = []
constructDescriptor _ _ _ = error "constructDescriptor: type not a list"


nestList :: Type -> [Int] -> [(Int, Norm)] -> ([Norm], [(Int, Norm)])
nestList t ps'@(p:ps) ls@((d,n):lists) | p == d = n `combine` (nestList t ps lists)
                                       | p <  d = ListN [] t `combine` (nestList t ps ls)
                                       | p >  d = nestList t ps' lists
nestList t (_:ps)     []                         = ListN [] t `combine` (nestList t ps [])
nestList _ []         ls                         = ([], ls)
nestList _ _ _ = error "nestList $ Not a neted list"

combine :: Norm -> ([Norm], [(Int, Norm)]) -> ([Norm], [(Int, Norm)])
combine n (ns, r) = (n:ns, r)


concatN :: Type -> [Norm] -> Norm
concatN _ ns@((ListN _ t1):_) = foldl' (\(ListN e t) (ListN e1 _) -> ListN (e1 ++ e) t) (ListN [] t1) ns
concatN t []                  = ListN [] t
concatN _ _                   = error "concatN: Not a list of lists"

normaliseList :: Type -> Int -> [(Int, [(Int, [SqlValue])])] -> [(Int, Norm)]
normaliseList t@(ListT t1) c vs = reverse $ foldl' (\tl (i, v) -> (i, ListN (map ((normalise t1 c) . snd) v) t):tl) [] vs
normaliseList _            _ _  = error "normaliseList: Should not happen"

normaliseX100List :: Type -> Int -> [(Int, [(Int, [X100Data])])] -> [(Int, Norm)]
normaliseX100List t@(ListT t1) index vs = reverse $ foldl' (\tl (i, v) -> (i, ListN (map ((normaliseX100 t1) . (!! (index - 1)) . snd) v) t):tl) [] vs
normaliseX100List _ _ _ = error "normaliseX100List: Should not happen"

normalise :: Type -> Int -> [SqlValue] -> Norm
normalise UnitT _ _ = UnitN UnitT
normalise t i v = convert (v !! i, t)

normaliseX100 :: Type -> X100Data -> Norm
normaliseX100 UnitT _ = UnitN UnitT
normaliseX100 t v = convert (v, t)

instance Convertible (X100Data, Type) Norm where
    safeConvert (Str s, TextT) = Right $ TextN (pack s) TextT
    safeConvert (Str s, CharT) = Right $ CharN (head s) CharT
    safeConvert (UChr i, BoolT) = Right $ BoolN (i /= 0) BoolT
    safeConvert (SChr i, BoolT) = Right $ BoolN (i /= 0) BoolT
    safeConvert (SInt i, BoolT) = Right $ BoolN (i /= 0) BoolT
    safeConvert (UInt i, BoolT) = Right $ BoolN (i /= 0) BoolT
    safeConvert (SSht i, BoolT) = Right $ BoolN (i /= 0) BoolT
    safeConvert (USht i, BoolT) = Right $ BoolN (i /= 0) BoolT
    safeConvert (SLng i, BoolT) = Right $ BoolN (i /= 0) BoolT
    safeConvert (ULng i, BoolT) = Right $ BoolN (i /= 0) BoolT
    safeConvert (UIDX i, BoolT) = Right $ BoolN (i /= 0) BoolT
    safeConvert (SInt i, IntegerT) = Right $ IntegerN (toInteger i) IntegerT
    safeConvert (UInt i, IntegerT) = Right $ IntegerN (toInteger i) IntegerT
    safeConvert (SChr i, IntegerT) = Right $ IntegerN (toInteger i) IntegerT
    safeConvert (UChr i, IntegerT) = Right $ IntegerN (toInteger i) IntegerT
    safeConvert (SSht i, IntegerT) = Right $ IntegerN (toInteger i) IntegerT
    safeConvert (USht i, IntegerT) = Right $ IntegerN (toInteger i) IntegerT
    safeConvert (SLng i, IntegerT) = Right $ IntegerN i IntegerT
    safeConvert (ULng i, IntegerT) = Right $ IntegerN i IntegerT
    safeConvert (UIDX i, IntegerT) = Right $ IntegerN i IntegerT
    safeConvert (Dbl d, DoubleT) = Right $ DoubleN d DoubleT
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
schemeToResult :: P.Schema -> [(String, SqlColDesc)] -> ResultInfo
schemeToResult (itN, col) resDescr = let resColumns = flip zip [0..] $ map (\(c, _) -> takeWhile (\a -> a /= '_') c) resDescr
                                         itC = fromJust $ lookup itN resColumns
                                      in (itC, map (\(n, _) -> (n, fromJust $ lookup n resColumns)) col)
