module Ferry.Interpreter (fromQ) where

import Ferry.Data
import Ferry.Impossible

import Data.Convertible
import Database.HDBC
import GHC.Exts

import Data.List

-- * Convert DB queries into Haskell values
fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q a) = evaluate c a >>= (return . fromNorm)

evaluate :: IConnection conn
         => conn                -- ^ The HDBC connection
         -> Exp
         -> IO Norm
evaluate c e = case e of
  UnitE     -> return UnitN
  BoolE b   -> return (BoolN b)
  CharE ch  -> return (CharN ch)
  IntE i    -> return (IntN i)
  DoubleE d -> return (DoubleN d)
  
  VarE _ -> $impossible
  LamE _ -> $impossible
  AppE f1 e1 -> evaluate c (f1 e1)

  TupleE e1 e2 -> do
    e3 <- evaluate c e1
    e4 <- evaluate c e2
    return (TupleN e3 e4)

  ListE es -> mapM (evaluate c) es >>= (return . ListN)
  
  AppE3 Cond cond a b -> do
      (BoolN c1) <- evaluate c cond
      if c1 then evaluate c a else evaluate c b 
  
  AppE2 Cons a as -> do
    a1 <- evaluate c a
    (ListN as1) <- evaluate c as
    return $ ListN $ a1 : as1

  AppE2 Snoc as a -> do
    a1 <- evaluate c a
    (ListN as1) <- evaluate c as
    return $ ListN $ snoc as1 a1

  AppE1 Head as -> do
    (ListN as1) <- evaluate c as
    return $ head as1

  AppE1 Tail as -> do
    (ListN as1) <- evaluate c as
    return $ ListN $ tail as1

  AppE2 Take i as -> do
    (IntN i1) <- evaluate c i
    (ListN as1) <- evaluate c as
    return $ ListN $ take i1 as1

  AppE2 Drop i as -> do
    (IntN i1) <- evaluate c i
    (ListN as1) <- evaluate c as
    return $ ListN $ drop i1 as1

  AppE2 Map lam as -> do
    (ListN as1) <- evaluate c as
    evaluate c $ ListE $ map (evalLam lam) as1

  AppE2 Append as bs -> do
    (ListN as1) <- evaluate c as
    (ListN bs1) <- evaluate c bs
    return $ ListN $ as1 ++ bs1

  AppE2 Filter lam as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalLam lam) as1)
    return $ ListN $ filter (\(BoolN b) -> b) as2

  AppE2 GroupWith lam as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalLam lam) as1)
    return $ ListN $ map (ListN . (map fst)) $ groupWith snd $ zip as1 as2

  AppE2 SortWith lam as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalLam lam) as1)
    return $ ListN $ map fst $ sortWith snd $ zip as1 as2

  AppE1 The as -> do
    (ListN as1) <- evaluate c as
    return $ the as1

  AppE1 Last as -> do
    (ListN as1) <- evaluate c as
    return $ last as1

  AppE1 Init as -> do
    (ListN as1) <- evaluate c as
    return $ ListN $ init as1

  AppE1 Null as -> do
    (ListN as1) <- evaluate c as
    return $ BoolN $ null as1

  AppE1 Length as -> do
    (ListN as1) <- evaluate c as
    return $ IntN $ length as1

  AppE2 Index as i -> do
    (IntN i1) <- evaluate c i
    (ListN as1) <- evaluate c as
    return $ as1 !! i1

  AppE1 Reverse as -> do
    (ListN as1) <- evaluate c as
    return $ ListN $ reverse as1

  AppE1 And as -> do
    (ListN as1) <- evaluate c as
    return $ BoolN $ and $ map (\(BoolN b) -> b) as1

  AppE1 Or as -> do
    (ListN as1) <- evaluate c as
    return $ BoolN $ or $ map (\(BoolN b) -> b) as1

  AppE2 Any lam as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalLam lam) as1)
    return $ BoolN $ any id $ map (\(BoolN b) -> b) as2

  AppE2 All lam as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalLam lam) as1)
    return $ BoolN $ all id $ map (\(BoolN b) -> b) as2

  AppE1 Sum as -> do
    (ListN as1) <- evaluate c as
    return $ IntN $ sum $ map (\(IntN i) -> i) as1

  AppE1 Product as -> do
    (ListN as1) <- evaluate c as
    return $ IntN $ product $ map (\(IntN i) -> i) as1

  AppE1 Concat as -> do
    (ListN as1) <- evaluate c as
    return $ ListN $ concat $ map (\(ListN as2) -> as2) as1

  AppE1 Maximum as -> do
    (ListN as1) <- evaluate c as
    return $ maximum as1

  AppE1 Minimum as -> do
    (ListN as1) <- evaluate c as
    return $ minimum as1

  AppE2 Replicate i a -> do
    (IntN i1) <- evaluate c i
    a1 <- evaluate c a
    return $ ListN $ replicate i1 a1

  AppE2 SplitAt i as -> do
    (IntN i1) <- evaluate c i
    (ListN as1) <- evaluate c as
    let t = splitAt i1 as1
    return $ TupleN (ListN $ fst t) (ListN $ snd t)

  AppE2 TakeWhile lam as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalLam lam) as1)
    return $ ListN $ map fst $ takeWhile (\(_,BoolN b) -> b) $ zip as1 as2

  AppE2 DropWhile lam as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalLam lam) as1)
    return $ ListN $ map fst $ dropWhile (\(_,BoolN b) -> b) $ zip as1 as2

  AppE2 Span lam as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalLam lam) as1)
    return $ (\(a,b) -> TupleN a b) $ (\(a,b) -> (ListN $ map fst a, ListN $ map fst b)) $ span (\(_,BoolN b) -> b) $ zip as1 as2

  AppE2 Break lam as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalLam lam) as1)
    return $ (\(a,b) -> TupleN a b) $ (\(a,b) -> (ListN $ map fst a, ListN $ map fst b)) $ break (\(_,BoolN b) -> b) $ zip as1 as2

  AppE2 Elem a as -> do
    a1 <- evaluate c a
    (ListN as1) <- evaluate c as
    return $ BoolN $ elem a1 as1

  AppE2 Zip as bs -> do
    (ListN as1) <- evaluate c as
    (ListN bs1) <- evaluate c bs
    return $ ListN $ zipWith (\a b -> TupleN a b) as1 bs1

  AppE1 Unzip as -> do
    (ListN as1) <- evaluate c as
    return $ TupleN (ListN $ map (\(TupleN a _) -> a) as1) (ListN $ map (\(TupleN _ b) -> b) as1)

  AppE3 ZipWith lam as bs -> do
    (ListN as1) <- evaluate c as
    (ListN bs1) <- evaluate c bs
    evaluate c $ ListE $ zipWith (\a b -> let lam1 = ((evalLam lam) a) in (evalLam lam1) b) as1 bs1

  AppE1 Nub as -> do
    (ListN as1) <- evaluate c as
    return $ ListN $ nub as1

  AppE1 Fst a -> do
    (TupleN a1 _) <- evaluate c a
    return a1

  AppE1 Snd a -> do
    (TupleN _ a1) <- evaluate c a
    return a1

  AppE2 Add e1 e2 ::: IntT -> do
    (IntN i1) <- evaluate c e1
    (IntN i2) <- evaluate c e2
    return $ IntN $ i1 + i2
  AppE2 Add e1 e2 ::: DoubleT -> do
    (DoubleN i1) <- evaluate c e1
    (DoubleN i2) <- evaluate c e2
    return $ DoubleN $ i1 + i2
  AppE2 Add _ _ -> $impossible

  AppE2 Mul e1 e2 ::: IntT -> do
    (IntN i1) <- evaluate c e1
    (IntN i2) <- evaluate c e2
    return $ IntN $ i1 * i2
  AppE2 Mul e1 e2 ::: DoubleT -> do
    (DoubleN i1) <- evaluate c e1
    (DoubleN i2) <- evaluate c e2
    return $ DoubleN $ i1 * i2
  AppE2 Mul _ _ -> $impossible

  AppE1 Abs e1 ::: IntT -> do
    (IntN i1) <- evaluate c e1
    return $ IntN $ abs i1
  AppE1 Abs e1 ::: DoubleT -> do
    (DoubleN i1) <- evaluate c e1
    return $ DoubleN $ abs i1
  AppE1 Abs _ -> $impossible

  AppE1 Negate e1 ::: IntT -> do
    (IntN i1) <- evaluate c e1
    return $ IntN $ negate i1
  AppE1 Negate e1 ::: DoubleT -> do
    (DoubleN i1) <- evaluate c e1
    return $ DoubleN $ negate i1
  AppE1 Negate _ -> $impossible

  AppE1 Signum e1 ::: IntT -> do
    (IntN i1) <- evaluate c e1
    return $ IntN $ signum i1
  AppE1 Signum e1 ::: DoubleT -> do
    (DoubleN i1) <- evaluate c e1
    return $ DoubleN $ signum i1
  AppE1 Signum _ -> $impossible

  AppE2 Equ e1 e2 -> do
    e3 <- evaluate c e1
    e4 <- evaluate c e2
    return $ BoolN $ e3 == e4

  AppE2 Lt e1 e2 -> do
    e3 <- evaluate c e1
    e4 <- evaluate c e2
    return $ BoolN $ e3 < e4

  AppE2 Lte e1 e2 -> do
    e3 <- evaluate c e1
    e4 <- evaluate c e2
    return $ BoolN $ e3 <= e4

  AppE2 Gte e1 e2 -> do
    e3 <- evaluate c e1
    e4 <- evaluate c e2
    return $ BoolN $ e3 >= e4

  AppE2 Gt e1 e2 -> do
    e3 <- evaluate c e1
    e4 <- evaluate c e2
    return $ BoolN $ e3 > e4

  AppE1 Not e1 -> do
    (BoolN b1) <- evaluate c e1
    return $ BoolN $ not b1 

  AppE2 Conj e1 e2 -> do
    (BoolN b1) <- evaluate c e1
    (BoolN b2) <- evaluate c e2
    return $ BoolN $ b1 && b2 

  AppE2 Disj e1 e2 -> do
    (BoolN b1) <- evaluate c e1
    (BoolN b2) <- evaluate c e2
    return $ BoolN $ b1 || b2 

  TableE tName ::: (ListT tType) -> do
      fmap (sqlToNormWithType tName tType)
           (quickQuery' c ("SELECT * FROM \"" ++ escape tName ++ "\"") [])
  TableE _ -> $impossible
  e1 ::: _ -> evaluate c e1 

snoc :: [a] -> a -> [a]
snoc [] a = [a]
snoc (b : bs) a = b : snoc bs a

escape :: String -> String
escape []                  = []
escape (c : cs) | c == '"' = '\\' : '"' : escape cs
escape (c : cs)            =          c : escape cs

evalLam :: Exp -> (Norm -> Exp)
evalLam (LamE f) n = f (convert n)
evalLam _ _ = $impossible


-- | Read SQL values into 'Norm' values
sqlToNormWithType :: String             -- ^ Table name, used to generate more
                                        -- informative error messages
                  -> Type
                  -> [[SqlValue]]
                  -> Norm
sqlToNormWithType tName ty = ListN . map (sqlValueToNorm ty)

  where
    sqlValueToNorm :: Type -> [SqlValue] -> Norm

    -- On a single value, just compare the 'Type' and convert the 'SqlValue' to
    -- a Norm value on match
    sqlValueToNorm t [s] = if t `typeMatch` s
                      then convert s
                      else typeError t [s]

    -- On more than one value we need a 'TupleT' type of the exact same length
    sqlValueToNorm t s | length (unfoldType t) == length s =
            let f t' s' = if t' `typeMatch` s'
                             then convert s'
                             else typeError t s
            in foldr1 TupleN (zipWith f (unfoldType t) s)

    -- Everything else will raise an error
    sqlValueToNorm t s = typeError t s

    typeError :: Type -> [SqlValue] -> a
    typeError t s = error $
        "ferry: Type mismatch on table \"" ++ tName ++ "\":"
        ++ "\n\tExpected table type: " ++ show t
        ++ "\n\tTable entry: " ++ show s


-- | Check if a 'SqlValue' matches a 'Type'
typeMatch :: Type -> SqlValue -> Bool
typeMatch t s =
    case (t,s) of
         (UnitT         , SqlNull)          -> True
         (IntT          , SqlInteger _)     -> True
         (BoolT         , SqlBool _)        -> True
         (CharT         , SqlChar _)        -> True
         (ListT CharT   , SqlString _)      -> True
         (ListT CharT   , SqlByteString _)  -> True
         _                                  -> False
