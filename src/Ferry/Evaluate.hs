{-# Options -fno-warn-incomplete-patterns #-}

module Ferry.Evaluate where

import Ferry.Data

import GHC.Exts

type Conn = ()

evaluate :: Conn -> Exp -> IO Norm
evaluate c e = case e of
  UnitE -> return UnitN
  BoolE b -> return (BoolN b)
  CharE ch -> return (CharN ch)
  IntE i -> return (IntN i)
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
    return $ ListN $ filter ((BoolN True) ==) as2
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
    return $ (a1 : b1 : as) !! (read $ snd $ break ('_' ==) is)

  TableE _s _t -> error "ferry: table combinator is not supported yet"
  
evalF :: (Exp -> Exp) -> (Norm -> Exp)
evalF f n = f (normToExp n)
