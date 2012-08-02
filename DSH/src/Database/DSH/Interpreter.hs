-- | This module provides the reference implementation of DSH by interpreting
-- the embedded representation.

{-# LANGUAGE TemplateHaskell, ViewPatterns, ScopedTypeVariables, GADTs #-}
{- # OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Database.DSH.Interpreter (fromQ) where

import Database.DSH.Data
import Database.DSH.Impossible (impossible)
import Database.DSH.CSV (csvImport)


import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Database.HDBC
import GHC.Exts
import Data.List

fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c a = evaluate c (qToExp a) >>= (return . fromNorm)

evaluate :: IConnection conn
         => conn                -- ^ The HDBC connection
         -> (Exp a)
         -> IO (Norm a)
evaluate c e = case e of
    UnitE -> return UnitN
    BoolE b -> return $ BoolN b
    CharE ch -> return $ CharN ch
    IntegerE i -> return $ IntegerN i
    DoubleE d -> return $ DoubleN d
    TextE t -> return $ TextN t 
    VarE _ -> $impossible
    Lam1E _ -> $impossible
    Lam2E _ -> $impossible
    PairE e1 e2 -> do
                     e1' <- evaluate c e1
                     e2' <- evaluate c e2
                     return (PairN e1' e2')
    ListE es -> do
                    es1 <- mapM (evaluate c) es
                    return $ ListN es1 
    App3E Cond cond a b -> do
      (BoolN c1) <- evaluate c cond
      if c1 then evaluate c a else evaluate c b
    AppH3E ZipWith lam as bs -> do
        (ListN as1) <- evaluate c as
        (ListN bs1) <- evaluate c bs
        evaluate c $ ListE (zipWith (\a b -> evalLam2 lam a b) as1 bs1)
    App2E Cons a as -> do
      a1 <- evaluate c a
      (ListN as1) <- evaluate c as
      return $ ListN (a1 : as1)
    App2E Snoc as a -> do
      a1 <- evaluate c a
      (ListN as1) <- evaluate c as
      return $ ListN (snoc as1 a1)
    App1E Head as -> do
      (ListN as1) <- evaluate c as
      return $ head as1
    App1E Tail as -> do
      (ListN as1) <- evaluate c as
      return $ ListN (tail as1)
    App2E Take i as -> do
      (IntegerN i1) <- evaluate c i
      (ListN as1) <- evaluate c as
      return $ ListN (take (fromIntegral i1) as1)
    App2E Drop i as -> do
      (IntegerN i1) <- evaluate c i
      (ListN as1) <- evaluate c as
      return $ ListN (drop (fromIntegral i1) as1)
    AppH2E Map lam as -> do
      (ListN as1) <- evaluate c as
      evaluate c $ ListE (map (evalLam1 lam) as1)
    App2E Append as bs -> do
      (ListN as1) <- evaluate c as
      (ListN bs1) <- evaluate c bs
      return $ ListN (as1 ++ bs1)
    AppH2E Filter lam as -> do
      (ListN as1) <- evaluate c as
      (ListN as2) <- evaluate c (ListE (map (evalLam1 lam) as1))
      return $ ListN (map fst (filter (\(_,(BoolN b)) -> b) (zip as1 as2))) 
    AppH2E GroupWith lam as -> do
      (ListN as1) <- evaluate c as
      (ListN as2) <- evaluate c (ListE (map (evalLam1 lam) as1))
      return $ ListN (map (ListN . (map fst)) $ groupWith snd $ zip as1 as2) 
    AppH2E SortWith (lam :: Exp (a -> b)) as -> do
      (ListN as1) <- evaluate c as
      (ListN as2) <- evaluate c $ ListE (map (evalLam1 lam) as1) 
      return $ ListN (map fst $ sortWith snd $ zip as1 as2)
    ((App2E Max e1 e2) :: Exp ty) -> do
      case reify (undefined :: ty) of
          IntegerT -> do
                        (IntegerN v1) <- evaluate c e1
                        (IntegerN v2) <- evaluate c e2
                        return $ IntegerN (max v1 v2)
          DoubleT -> do 
                        (DoubleN v1) <- evaluate c e1
                        (DoubleN v2) <- evaluate c e2
                        return $ DoubleN (max v1 v2)
          _ -> $impossible
    ((App2E Min e1 e2) :: Exp ty) -> do
      case reify (undefined :: ty) of
          IntegerT -> do
                        (IntegerN v1) <- evaluate c e1
                        (IntegerN v2) <- evaluate c e2
                        return $ IntegerN (min v1 v2)
          DoubleT -> do
                        (DoubleN v1) <- evaluate c e1
                        (DoubleN v2) <- evaluate c e2
                        return $ DoubleN (min v1 v2)
          _ -> $impossible
    App1E The as -> do
      (ListN as1) <- evaluate c as
      return $ the as1
    App1E Last as -> do
      (ListN as1) <- evaluate c as
      return $ last as1
    App1E Init as -> do
      (ListN as1) <- evaluate c as
      return $ ListN (init as1)
    App1E Null as -> do
      (ListN as1) <- evaluate c as
      return $ BoolN (null as1)
    App1E Length as -> do
     (ListN as1) <- evaluate c as
     return $ IntegerN (fromIntegral $ length as1)
    App2E Index as i -> do
     (IntegerN i1) <- evaluate c i
     (ListN as1) <- evaluate c as
     return $ as1 !! (fromIntegral i1)
    App1E Reverse as -> do
      (ListN as1) <- evaluate c as
      return $ ListN (reverse as1)
    App1E And as -> do
      (ListN as1) <- evaluate c as
      return $ BoolN (and $ map (\(BoolN b) -> b) as1)
    App1E Or as -> do
      (ListN as1) <- evaluate c as
      return $ BoolN (or $ map (\(BoolN b) -> b) as1)
    AppH2E Any lam as -> do
      (ListN as1) <- evaluate c as
      (ListN as2) <- evaluate c (ListE (map (evalLam1 lam) as1)) 
      return $ BoolN (any id $ map (\(BoolN b) -> b) as2) 
    AppH2E All lam as -> do
      (ListN as1) <- evaluate c as
      (ListN as2) <- evaluate c (ListE (map (evalLam1 lam) as1))
      return $ BoolN (all id $ map (\(BoolN b) -> b) as2)
    (App1E Sum as :: Exp ty) -> do
      let ty = reify (undefined :: ty)
      (ListN as1) <- evaluate c as
      case ty of
          IntegerT -> return $ IntegerN (sum $ map (\(IntegerN i) -> i) as1)
          DoubleT  -> return $ DoubleN (sum $ map (\(DoubleN d) -> d) as1)
          _ -> $impossible
    ((App1E Concat as) :: Exp ty) -> do
      let ty = reify (undefined :: ty)
      (ListN as1) <- evaluate c as
      -- Case analysis is necessary to convince the type checker that we can only have [[a]] here. It is not smart enough that there is just one type valid here...
      case ty of
          (ListT (ListT _)) -> return $ ListN (concat $ map (\(ListN as2) -> as2) as1)
          _ -> $impossible 
    App1E Maximum as -> do
      (ListN as1) <- evaluate c as
      return $ maximum as1
    App1E Minimum as -> do
      (ListN as1) <- evaluate c as
      return $ minimum as1
    App2E SplitAt i as -> do
      (IntegerN i1) <- evaluate c i
      (ListN as1) <- evaluate c as
      let r = splitAt (fromIntegral i1) as1
      return $ PairN (ListN (fst r)) (ListN (snd r)) 
    AppH2E TakeWhile lam as -> do
      (ListN as1) <- evaluate c as
      (ListN as2) <- evaluate c (ListE (map (evalLam1 lam) as1))
      return $ ListN (map fst $ takeWhile (\(_,BoolN b) -> b) $ zip as1 as2)
    AppH2E DropWhile lam as -> do
      (ListN as1) <- evaluate c as
      (ListN as2) <- evaluate c (ListE (map (evalLam1 lam) as1))
      return $ ListN (map fst $ dropWhile (\(_,BoolN b) -> b) $ zip as1 as2)
    AppH2E Span lam as -> do
      (ListN as1) <- evaluate c as
      (ListN as2) <- evaluate c (ListE (map (evalLam1 lam) as1))
      return $ (\(a,b) -> PairN a b)
             $ (\(a,b) -> (ListN (map fst a), ListN (map fst b)))
             $ span (\(_,BoolN b) -> b)
             $ zip as1 as2
    AppH2E Break lam as -> do
      (ListN as1) <- evaluate c as
      (ListN as2) <- evaluate c (ListE (map (evalLam1 lam) as1))
      return $ (\(a,b) -> PairN a b)
             $ (\(a,b) -> (ListN (map fst a), ListN (map fst b)))
             $ break (\(_,BoolN b) -> b)
             $ zip as1 as2
    App2E Zip as bs -> do
      (ListN as1) <- evaluate c as
      (ListN bs1) <- evaluate c bs
      return $ ListN (zipWith (\a b -> PairN a b) as1 bs1)
    ((App1E Unzip as) :: Exp ty) -> do
      let ty = reify (undefined :: ty)
      (ListN as1) <- evaluate c as
      -- Case analysis to convince the type checker
      case ty of
          (PairT (ListT _) (ListT _)) -> return $ PairN (ListN (map (\(PairN a _) -> a) as1))
                                                (ListN (map (\(PairN _ b) -> b) as1)) 
          _ -> $impossible
    App1E Nub as -> do
      (ListN as1) <- evaluate c as
      return $ ListN (nub as1)
    App1E Fst a -> do
      (PairN a1 _) <- evaluate c a
      return a1
    App1E Snd a -> do
      (PairN _ a1) <- evaluate c a
      return a1
    ((App2E Add e1 e2) :: Exp ty) -> do
      let ty = reify (undefined :: ty)
      case ty of
         IntegerT -> do
                      (IntegerN i1) <- evaluate c e1
                      (IntegerN i2) <- evaluate c e2
                      return $ IntegerN (i1 + i2)
         DoubleT  -> do
                      (DoubleN d1) <- evaluate c e1
                      (DoubleN d2) <- evaluate c e2
                      return $ DoubleN (d1 + d2)
         _ -> $impossible
    ((App2E Sub e1 e2) :: Exp ty) -> do
      let ty = reify (undefined :: ty)
      case ty of
         IntegerT -> do
                      (IntegerN i1) <- evaluate c e1
                      (IntegerN i2) <- evaluate c e2
                      return $ IntegerN (i1 - i2)
         DoubleT  -> do
                      (DoubleN d1) <- evaluate c e1
                      (DoubleN d2) <- evaluate c e2
                      return $ DoubleN (d1 - d2)
         _ -> $impossible
    ((App2E Mul e1 e2) :: Exp ty) -> do
      let ty = reify (undefined :: ty)
      case ty of
         IntegerT -> do
                      (IntegerN i1) <- evaluate c e1
                      (IntegerN i2) <- evaluate c e2
                      return $ IntegerN (i1 * i2)
         DoubleT  -> do
                      (DoubleN d1) <- evaluate c e1
                      (DoubleN d2) <- evaluate c e2
                      return $ DoubleN (d1 * d2)
         _ -> $impossible
    ((App2E Div e1 e2) :: Exp ty) -> do
      let ty = reify (undefined :: ty)
      case ty of
         DoubleT  -> do
                      (DoubleN d1) <- evaluate c e1
                      (DoubleN d2) <- evaluate c e2
                      return $ DoubleN (d1 / d2)
         _ -> $impossible
    App1E IntegerToDouble e1 -> do
      (IntegerN i1) <- evaluate c e1
      return $ DoubleN (fromInteger i1)
    App2E Equ e1 e2 -> do
      e3 <- evaluate c e1
      e4 <- evaluate c e2
      return $ BoolN (e3 == e4)
    App2E Lt e1 e2 -> do
      e3 <- evaluate c e1
      e4 <- evaluate c e2
      return $ BoolN (e3 < e4) 
    App2E Lte e1 e2 -> do
      e3 <- evaluate c e1
      e4 <- evaluate c e2
      return $ BoolN (e3 <= e4)
    App2E Gte e1 e2 -> do
      e3 <- evaluate c e1
      e4 <- evaluate c e2
      return $ BoolN (e3 >= e4) 
    App2E Gt e1 e2 -> do
      e3 <- evaluate c e1
      e4 <- evaluate c e2
      return $ BoolN (e3 > e4) 
    App1E Not e1 -> do
      (BoolN b1) <- evaluate c e1
      return $ BoolN (not b1)
    App2E Conj e1 e2 -> do
      (BoolN b1) <- evaluate c e1
      (BoolN b2) <- evaluate c e2
      return $ BoolN (b1 && b2)
    App2E Disj e1 e2 -> do
      (BoolN b1) <- evaluate c e1
      (BoolN b2) <- evaluate c e2
      return $ BoolN (b1 || b2) 
    ((TableE (TableDB (escape -> tName) _)) :: Exp ty) -> 
      let ty = reify (undefined :: ty)
      in case ty of
          ListT tType -> do
            tDesc <- describeTable c tName
            let columnNames = concat $ intersperse " , " $ map (\s -> "\"" ++ s ++ "\"") $ sort $ map fst tDesc
            let query = "SELECT " ++ columnNames ++ " FROM " ++ "\"" ++ tName ++ "\""
            -- print query
            fmap (sqlToNormWithType tName tType) (quickQuery c query [])
          _ -> $impossible
    ((TableE (TableCSV filename)) :: Exp ty) -> csvImport filename (reify (undefined :: ty))

snoc :: [a] -> a -> [a]
snoc [] a = [a]
snoc (b : bs) a = b : snoc bs a

escape :: String -> String
escape []                  = []
escape (c : cs) | c == '"' = '\\' : '"' : escape cs
escape (c : cs)            =          c : escape cs

evalLam1 :: (QA a, QA b) => Exp (a -> b) -> (Norm a -> Exp b)
evalLam1 (Lam1E f) n = f (normToExp n)
evalLam1 _ _ = $impossible

evalLam2 :: (QA a, QA b, QA c) => Exp (a -> b -> c) -> Norm a -> Norm b -> Exp c
evalLam2 (Lam2E f) n1 n2 = f (normToExp n1) (normToExp n2)
evalLam2 _ _ _ = $impossible

-- | Read SQL values into 'Norm' values
sqlToNormWithType :: QA a => String             -- ^ Table name, used to generate more
                                        -- informative error messages
                  -> Type a
                  -> [[SqlValue]]
                  -> Norm [a]
sqlToNormWithType tName ty = ListN . map (sqlValueToNorm ty)
  where
    sqlValueToNorm :: QA a => Type a -> [SqlValue] -> Norm a
    sqlValueToNorm (PairT t1 t2) s = let v1 = sqlValueToNorm t1 $ take (sizeOfType t1) s
                                         v2 = sqlValueToNorm t2 $ drop (sizeOfType t1) s
                                      in PairN v1 v2
    -- On a single value, just compare the 'Type' and convert the 'SqlValue' to
    -- a Norm value on match
    sqlValueToNorm t [s] = if t `typeMatch` s
                      then convert s t
                      else typeError t [s]
    -- Everything else will raise an error
    sqlValueToNorm t s = typeError t s

    typeError :: Type a -> [SqlValue] -> b
    typeError t s = error $
        "ferry: Type mismatch on table \"" ++ tName ++ "\":"
        ++ "\n\tExpected table type: " ++ show t
        ++ "\n\tTable entry: " ++ show s

convert :: SqlValue -> Type a -> Norm a
convert SqlNull UnitT = UnitN
convert (SqlInteger i) IntegerT = IntegerN i 
convert (SqlDouble d)  DoubleT  = DoubleN d 
convert (SqlBool b) BoolT       = BoolN b 
convert (SqlChar c) CharT       = CharN c 
convert (SqlString t) TextT     = TextN (T.pack t) 
convert (SqlByteString s) TextT = TextN (T.decodeUtf8 s)
convert sql                 _     = error "Unsupported `SqlValue'" sql

sizeOfType :: Type a -> Int
sizeOfType UnitT = 1
sizeOfType IntegerT = 1
sizeOfType DoubleT = 1
sizeOfType BoolT = 1
sizeOfType CharT = 1
sizeOfType TextT = 1
sizeOfType (PairT t1 t2) = sizeOfType t1 + sizeOfType t2
sizeOfType _ = error "sizeOfType: Not a record type"

-- | Check if a 'SqlValue' matches a 'Type'
typeMatch :: Type a -> SqlValue -> Bool
typeMatch t s =
    case (t,s) of
         (UnitT         , SqlNull)          -> True
         (IntegerT      , SqlInteger _)     -> True
         (DoubleT       , SqlDouble _)      -> True
         (BoolT         , SqlBool _)        -> True
         (CharT         , SqlChar _)        -> True
         (TextT         , SqlString _)      -> True
         (TextT         , SqlByteString _)  -> True
         _                                  -> False