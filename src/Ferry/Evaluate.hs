{-# LANGUAGE TemplateHaskell, RelaxedPolyRec #-}
{-# Options -fno-warn-incomplete-patterns #-}

module Ferry.Evaluate where

import Ferry.Data

import Database.HDBC
import GHC.Exts


evaluate :: IConnection conn
         => conn                -- ^ The HDBC connection
         -> Exp
         -> IO Norm
evaluate c e = case e of
  UnitE    -> return UnitN
  BoolE b  -> return (BoolN b)
  CharE ch -> return (CharN ch)
  IntE i   -> return (IntN i)

  TupleE e1 e2 es1 -> do
    e3 <- evaluate c e1
    e4 <- evaluate c e2
    es2 <- mapM (evaluate c) es1
    return (TupleN e3 e4 es2)

  ListE es -> mapM (evaluate c) es >>= (return . ListN)
  
  AppE (AppE (VarE "cons") a) as -> do
    a1 <- evaluate c a
    (ListN as1) <- evaluate c as
    return $ ListN $ a1 : as1

  AppE (VarE "head") as -> do
    (ListN as1) <- evaluate c as
    return $ head as1

  AppE (VarE "tail") as -> do
    (ListN as1) <- evaluate c as
    return $ ListN $ tail as1

  AppE (AppE (VarE "take") i) as -> do
    (IntN i1) <- evaluate c i
    (ListN as1) <- evaluate c as
    return $ ListN $ take i1 as1

  AppE (AppE (VarE "drop") i) as -> do
    (IntN i1) <- evaluate c i
    (ListN as1) <- evaluate c as
    return $ ListN $ drop i1 as1

  AppE (AppE (VarE "map") (FuncE f)) as -> do
    (ListN as1) <- evaluate c as
    evaluate c $ ListE $ map (evalF f) as1

  AppE (AppE (VarE "append") as) bs -> do
    (ListN as1) <- evaluate c as
    (ListN bs1) <- evaluate c bs
    return $ ListN $ as1 ++ bs1

  AppE (AppE (VarE "filter") (FuncE f)) as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalF f) as1)
    return $ ListN $ filter (\(BoolN b) -> b) as2

  AppE (AppE (VarE "groupWith") (FuncE f)) as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalF f) as1)
    return $ ListN $ map (ListN . (map fst)) $ groupWith snd $ zip as1 as2

  AppE (AppE (VarE "sortWith") (FuncE f)) as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalF f) as1)
    return $ ListN $ map fst $ sortWith snd $ zip as1 as2

  AppE (VarE "the") as -> do
    (ListN as1) <- evaluate c as
    return $ the as1

  AppE (VarE "last") as -> do
    (ListN as1) <- evaluate c as
    return $ last as1

  AppE (VarE "init") as -> do
    (ListN as1) <- evaluate c as
    return $ ListN $ init as1

  AppE (VarE "null") as -> do
    (ListN as1) <- evaluate c as
    return $ BoolN $ null as1

  AppE (VarE "length") as -> do
    (ListN as1) <- evaluate c as
    return $ IntN $ length as1

  AppE (AppE (VarE "index") as) i -> do
    (IntN i1) <- evaluate c i
    (ListN as1) <- evaluate c as
    return $ as1 !! i1

  AppE (VarE "reverse") as -> do
    (ListN as1) <- evaluate c as
    return $ ListN $ reverse as1

  AppE (VarE "and") as -> do
    (ListN as1) <- evaluate c as
    return $ BoolN $ and $ map (\(BoolN b) -> b) as1

  AppE (VarE "or") as -> do
    (ListN as1) <- evaluate c as
    return $ BoolN $ or $ map (\(BoolN b) -> b) as1

  AppE (AppE (VarE "any") (FuncE f)) as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalF f) as1)
    return $ BoolN $ any id $ map (\(BoolN b) -> b) as2

  AppE (AppE (VarE "all") (FuncE f)) as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalF f) as1)
    return $ BoolN $ all id $ map (\(BoolN b) -> b) as2

  AppE (VarE "sum") as -> do
    (ListN as1) <- evaluate c as
    return $ IntN $ sum $ map (\(IntN i) -> i) as1

  AppE (VarE "product") as -> do
    (ListN as1) <- evaluate c as
    return $ IntN $ product $ map (\(IntN i) -> i) as1

  AppE (VarE "concat") as -> do
    (ListN as1) <- evaluate c as
    return $ ListN $ concat $ map (\(ListN as2) -> as2) as1

  AppE (AppE (VarE "concatMap") (FuncE f)) as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalF f) as1)
    return $ ListN $ concat $ map (\(ListN as3) -> as3) as2

  AppE (VarE "maximum") as -> do
    (ListN as1) <- evaluate c as
    return $ maximum as1

  AppE (VarE "minimum") as -> do
    (ListN as1) <- evaluate c as
    return $ minimum as1

  AppE (AppE (VarE "replicate") i) a -> do
    (IntN i1) <- evaluate c i
    a1 <- evaluate c a
    return $ ListN $ replicate i1 a1

  AppE (AppE (VarE "splitAt") i) as -> do
    (IntN i1) <- evaluate c i
    (ListN as1) <- evaluate c as
    let t = splitAt i1 as1 
    return $ TupleN (ListN $ fst t) (ListN $ snd t) []

  AppE (AppE (VarE "takeWhile") (FuncE f)) as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalF f) as1)
    return $ ListN $ map fst $ takeWhile (\(_,BoolN b) -> b) $ zip as1 as2 

  AppE (AppE (VarE "dropWhile") (FuncE f)) as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalF f) as1)
    return $ ListN $ map fst $ dropWhile (\(_,BoolN b) -> b) $ zip as1 as2

  AppE (AppE (VarE "span") (FuncE f)) as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalF f) as1)
    return $ (\(a,b) -> TupleN a b []) $ (\(a,b) -> (ListN $ map fst a, ListN $ map fst b)) $ span (\(_,BoolN b) -> b) $ zip as1 as2

  AppE (AppE (VarE "break") (FuncE f)) as -> do
    (ListN as1) <- evaluate c as
    (ListN as2) <- evaluate c (ListE $ map (evalF f) as1)
    return $ (\(a,b) -> TupleN a b []) $ (\(a,b) -> (ListN $ map fst a, ListN $ map fst b)) $ break (\(_,BoolN b) -> b) $ zip as1 as2

  AppE (AppE (VarE "elem") a) as -> do
    a1 <- evaluate c a
    (ListN as1) <- evaluate c as
    return $ BoolN $ elem a1 as1

  AppE (AppE (VarE "notElem") a) as -> do
    a1 <- evaluate c a
    (ListN as1) <- evaluate c as
    return $ BoolN $ notElem a1 as1

  AppE (AppE (VarE "zip") as) bs -> do
    (ListN as1) <- evaluate c as
    (ListN bs1) <- evaluate c bs
    return $ ListN $ zipWith (\a b -> TupleN a b []) as1 bs1

  AppE (VarE "unzip") as -> do
    (ListN as1) <- evaluate c as
    return $ TupleN (ListN $ map (\(TupleN a _ _) -> a) as1) (ListN $ map (\(TupleN _ b _) -> b) as1) []

  AppE (AppE (AppE (VarE "zipWith") (FuncE f)) as) bs -> do
    (ListN as1) <- evaluate c as
    (ListN bs1) <- evaluate c bs
    evaluate c $ ListE $ zipWith (\a b -> let (FuncE f1) = ((evalF f) a) in (evalF f1) b) as1 bs1

  AppE (VarE ('p' : 'r' : 'o' : 'j' : '_' : is)) a -> do
    (TupleN a1 b1 as) <- evaluate c a
    let i = read $ tail $ snd $ break ('_' ==) is
    return $ (a1 : b1 : as) !! (i - 1)

  AppE (AppE (VarE "add") e1) e2 -> do
    (IntN i1) <- evaluate c e1
    (IntN i2) <- evaluate c e2
    return $ IntN $ i1 + i2

  AppE (AppE (VarE "mul") e1) e2 -> do
    (IntN i1) <- evaluate c e1
    (IntN i2) <- evaluate c e2
    return $ IntN $ i1 * i2

  AppE (VarE "abs") e1 -> do
    (IntN i1) <- evaluate c e1
    return $ IntN $ abs i1 

  AppE (VarE "negate") e1 -> do
    (IntN i1) <- evaluate c e1
    return $ IntN $ negate i1 

  AppE (VarE "signum") e1 -> do
    (IntN i1) <- evaluate c e1
    return $ IntN $ signum i1 

  TableE tName tType -> do

      -- escape tName/raise error if invalid table name?
      fmap (sqlToNormWithType tName tType)
           (quickQuery' c ("SELECT * from " ++ tName) [])


  
evalF :: (Exp -> Exp) -> (Norm -> Exp)
evalF f n = f (normToExp n)


-- | Read SQL values into 'Norm' values
sqlToNormWithType :: String             -- ^ Table name, used to generate more
                                        -- informative error messages
                  -> Type
                  -> [[SqlValue]]
                  -> Norm
sqlToNormWithType tName ty = ListN . map (toNorm ty)

  where
    toNorm :: Type -> [SqlValue] -> Norm

    -- On a single value, just compare the 'Type' and convert the 'SqlValue' to
    -- a Norm value on match
    toNorm t [s] = if t `typeMatch` s
                      then sqlToNorm s
                      else typeError t [s]

    -- On more than one value we need a 'TupleT' type of the exact same length
    toNorm (TupleT t@(_:_:_)) s
        | length t == length s =
            let (a:b:rest) = zipWith f t s
                f t' s' = if t' `typeMatch` s'
                             then sqlToNorm s'
                             else typeError (TupleT t) s
            in TupleN a b rest

    -- Everything else will raise an error
    toNorm t s = typeError t s

    typeError :: Type -> [SqlValue] -> a
    typeError t s = error $
        "ferry: Type mismatch on table \"" ++ tName ++ "\":"
        ++ "\n\tExpected table type: " ++ show t
        ++ "\n\tTable entry: " ++ show s


-- | Turn one single SqlValue into a Norm value
sqlToNorm :: SqlValue -> Norm
sqlToNorm sql =
    case sql of
         SqlNull        -> UnitN
         SqlInt32 i     -> IntN $ fromIntegral i
         SqlBool b      -> BoolN b
         SqlChar c      -> CharN c
         SqlString s    -> stringN s
         _              -> error $ "ferry: Unsupported SqlValue: " ++ show sql

  where stringN s = ListN $ map CharN s


-- | Check if a 'SqlValue' matches a 'Type'
typeMatch :: Type -> SqlValue -> Bool
typeMatch t s =
    case (t,s) of
         (UnitT         , SqlNull)      -> True
         (IntT          , SqlInt32 _)   -> True
         (BoolT         , SqlBool _)    -> True
         (CharT         , SqlChar _)    -> True
         (ListT CharT   , SqlString _)  -> True
         _                              -> False
