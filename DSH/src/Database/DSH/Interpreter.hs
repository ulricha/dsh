{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | This module provides the reference implementation of DSH by interpreting
-- the embedded representation.

module Database.DSH.Interpreter (fromQ) where

import Database.DSH.Internals
import Database.DSH.Impossible
import Database.DSH.CSV

import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Database.HDBC
import Data.List

fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q e) = fmap frExp (evaluate c e)

evaluate :: forall a conn. (Reify a, IConnection conn) => conn -> Exp a -> IO (Exp a)
evaluate c e = case e of
    UnitE -> return UnitE
    BoolE b -> return $ BoolE b
    CharE ch -> return $ CharE ch
    IntegerE i -> return $ IntegerE i
    DoubleE d -> return $ DoubleE d
    TextE t -> return $ TextE t 
    VarE _ -> $impossible
    LamE _ -> $impossible
    PairE e1 e2 -> do
      e1' <- evaluate c e1
      e2' <- evaluate c e2
      return (PairE e1' e2')
    ListE es -> do
       es1 <- mapM (evaluate c) es
       return $ ListE es1 
    AppE Cond (PairE cond (PairE a b)) -> do
      (BoolE c1) <- evaluate c cond
      if c1 then evaluate c a else evaluate c b
    AppE Cons (PairE a as) -> do
      a1 <- evaluate c a
      (ListE as1) <- evaluate c as
      return $ ListE (a1 : as1)
    AppE Head as -> do
      (ListE as1) <- evaluate c as
      return $ head as1
    AppE Tail as -> do
      (ListE as1) <- evaluate c as
      return $ ListE (tail as1)
    AppE Take (PairE i as) -> do
      (IntegerE i1) <- evaluate c i
      (ListE as1) <- evaluate c as
      return $ ListE (take (fromIntegral i1) as1)
    AppE Drop (PairE i as) -> do
      (IntegerE i1) <- evaluate c i
      (ListE as1) <- evaluate c as
      return $ ListE (drop (fromIntegral i1) as1)
    AppE Map (PairE (LamE f) as) -> do
      (ListE as1) <- evaluate c as
      evaluate c $ ListE (map f as1)
    AppE Filter (PairE (LamE f) as) -> do
      (ListE as1) <- evaluate c as
      (ListE as2) <- evaluate c (ListE (map f as1))
      return $ ListE (map fst (filter (\(_,BoolE b) -> b) (zip as1 as2))) 
    AppE GroupWithKey (PairE (LamE f) as) -> do
      (ListE as1) <- evaluate c as
      (ListE ks1) <- evaluate c (ListE (map f as1))
      return $ ListE
             $ map (\kas1 -> PairE (fst (head kas1)) (ListE (map snd kas1)))
             $ groupBy (\(k1,_) (k2,_) -> equExp k1 k2)
             $ sortBy (\(k1,_) (k2,_) -> compareExp k1 k2)
             $ zip ks1 as1
    AppE SortWith (PairE (LamE f) as) -> do
      (ListE as1) <- evaluate c as
      (ListE as2) <- evaluate c $ ListE (map f as1) 
      return $ ListE 
             $ map fst
             $ sortBy (\(_,a1) (_,a2) -> compareExp a1 a2)
             $ zip as1 as2
    (AppE Max (PairE e1 e2)) ->
      case reify (undefined :: a) of
          IntegerT -> do (IntegerE v1) <- evaluate c e1
                         (IntegerE v2) <- evaluate c e2
                         return $ IntegerE (max v1 v2)
          DoubleT  -> do (DoubleE v1) <- evaluate c e1
                         (DoubleE v2) <- evaluate c e2
                         return $ DoubleE (max v1 v2)
          _ -> $impossible
    (AppE Min (PairE e1 e2)) ->
      case reify (undefined :: a) of
          IntegerT -> do (IntegerE v1) <- evaluate c e1
                         (IntegerE v2) <- evaluate c e2
                         return $ IntegerE (min v1 v2)
          DoubleT  -> do (DoubleE v1) <- evaluate c e1
                         (DoubleE v2) <- evaluate c e2
                         return $ DoubleE (min v1 v2)
          _ -> $impossible
    AppE Last as -> do
      (ListE as1) <- evaluate c as
      return $ last as1
    AppE Init as -> do
      (ListE as1) <- evaluate c as
      return $ ListE (init as1)
    AppE Null as -> do
      (ListE as1) <- evaluate c as
      return $ BoolE (null as1)
    AppE Length as -> do
     (ListE as1) <- evaluate c as
     return $ IntegerE (fromIntegral $ length as1)
    AppE Index (PairE as i) -> do
     (IntegerE i1) <- evaluate c i
     (ListE as1) <- evaluate c as
     return $ as1 !! fromIntegral i1
    AppE Reverse as -> do
      (ListE as1) <- evaluate c as
      return $ ListE (reverse as1)
    AppE And as -> do
      (ListE as1) <- evaluate c as
      return $ BoolE (all (\(BoolE b) -> b) as1)
    AppE Or as -> do
      (ListE as1) <- evaluate c as
      return $ BoolE (any (\(BoolE b) -> b) as1)
    (AppE Sum as) -> do
      let ty = reify (undefined :: a)
      (ListE as1) <- evaluate c as
      case ty of
          IntegerT -> return $ IntegerE (sum $ map (\(IntegerE i) -> i) as1)
          DoubleT  -> return $ DoubleE (sum $ map (\(DoubleE d) -> d) as1)
          _ -> $impossible
    (AppE Avg _) -> undefined
    AppE Concat as -> do
      (ListE as1) <- evaluate c as
      return $ ListE (concatMap (\(ListE as2) -> as2) as1)
    AppE Maximum as -> do
      (ListE as1) <- evaluate c as
      return $ maximumBy compareExp as1
    AppE Minimum as -> do
      (ListE as1) <- evaluate c as
      return $ minimumBy compareExp as1
    AppE SplitAt (PairE i as) -> do
      (IntegerE i1) <- evaluate c i
      (ListE as1) <- evaluate c as
      let r = splitAt (fromIntegral i1) as1
      return $ PairE (ListE (fst r)) (ListE (snd r)) 
    AppE TakeWhile (PairE (LamE f) as) -> do
      (ListE as1) <- evaluate c as
      (ListE as2) <- evaluate c (ListE (map f as1))
      return $ ListE (map fst $ takeWhile (\(_,BoolE b) -> b) $ zip as1 as2)
    AppE DropWhile (PairE (LamE f) as) -> do
      (ListE as1) <- evaluate c as
      (ListE as2) <- evaluate c (ListE (map f as1))
      return $ ListE (map fst $ dropWhile (\(_,BoolE b) -> b) $ zip as1 as2)
    AppE Zip (PairE as bs) -> do
      (ListE as1) <- evaluate c as
      (ListE bs1) <- evaluate c bs
      return $ ListE (zipWith PairE as1 bs1)
    AppE Nub as -> do
      (ListE as1) <- evaluate c as
      return $ ListE (nubBy equExp as1)
    AppE Fst a -> do
      (PairE a1 _) <- evaluate c a
      return a1
    AppE Snd a -> do
      (PairE _ a1) <- evaluate c a
      return a1
    (AppE Add (PairE e1 e2)) -> do
      let ty = reify (undefined :: a)
      case ty of
         IntegerT -> do
                      (IntegerE i1) <- evaluate c e1
                      (IntegerE i2) <- evaluate c e2
                      return $ IntegerE (i1 + i2)
         DoubleT  -> do
                      (DoubleE d1) <- evaluate c e1
                      (DoubleE d2) <- evaluate c e2
                      return $ DoubleE (d1 + d2)
         _ -> $impossible
    (AppE Sub (PairE e1 e2)) -> do
      let ty = reify (undefined :: a)
      case ty of
         IntegerT -> do
                      (IntegerE i1) <- evaluate c e1
                      (IntegerE i2) <- evaluate c e2
                      return $ IntegerE (i1 - i2)
         DoubleT  -> do
                      (DoubleE d1) <- evaluate c e1
                      (DoubleE d2) <- evaluate c e2
                      return $ DoubleE (d1 - d2)
         _ -> $impossible
    (AppE Mul (PairE e1 e2)) -> do
      let ty = reify (undefined :: a)
      case ty of
         IntegerT -> do
                      (IntegerE i1) <- evaluate c e1
                      (IntegerE i2) <- evaluate c e2
                      return $ IntegerE (i1 * i2)
         DoubleT  -> do
                      (DoubleE d1) <- evaluate c e1
                      (DoubleE d2) <- evaluate c e2
                      return $ DoubleE (d1 * d2)
         _ -> $impossible
    (AppE Div (PairE e1 e2)) -> do
      let ty = reify (undefined :: a)
      case ty of
         DoubleT  -> do
                      (DoubleE d1) <- evaluate c e1
                      (DoubleE d2) <- evaluate c e2
                      return $ DoubleE (d1 / d2)
         _ -> $impossible
    AppE IntegerToDouble e1 -> do
      (IntegerE i1) <- evaluate c e1
      return $ DoubleE (fromInteger i1)
    AppE Equ (PairE e1 e2) -> do
      e3 <- evaluate c e1
      e4 <- evaluate c e2
      return $ BoolE $ equExp e3 e4
    AppE Lt (PairE e1 e2) -> do
      e3 <- evaluate c e1
      e4 <- evaluate c e2
      return $ BoolE $ ltExp e3 e4
    AppE Lte (PairE e1 e2) -> do
      e3 <- evaluate c e1
      e4 <- evaluate c e2
      return $ BoolE $ lteExp e3 e4
    AppE Gte (PairE e1 e2) -> do
      e3 <- evaluate c e1
      e4 <- evaluate c e2
      return $ BoolE $ gteExp e3 e4
    AppE Gt (PairE e1 e2) -> do
      e3 <- evaluate c e1
      e4 <- evaluate c e2
      return $ BoolE $ gtExp e3 e4
    AppE Not e1 -> do
      (BoolE b1) <- evaluate c e1
      return $ BoolE (not b1)
    AppE Conj (PairE e1 e2) -> do
      (BoolE b1) <- evaluate c e1
      (BoolE b2) <- evaluate c e2
      return $ BoolE (b1 && b2)
    AppE Disj (PairE e1 e2) -> do
      (BoolE b1) <- evaluate c e1
      (BoolE b2) <- evaluate c e2
      return $ BoolE (b1 || b2) 
    AppE Like (PairE te pe) -> do
      (TextE t) <- evaluate c te
      (TextE p) <- evaluate c pe
      return $ BoolE (matchPat t p)
    (TableE (TableDB tName _)) -> 
      let ty = reify (undefined :: a)
      in case ty of
          ListT tType -> do
            tDesc <- describeTable c (escape tName)
            let columnNames = intercalate " , " $ map (\s -> "\"" ++ s ++ "\"") $ sort $ map fst tDesc
            let query = "SELECT " ++ columnNames ++ " FROM " ++ "\"" ++ escape tName ++ "\""
            -- print query
            fmap (sqlToExpWithType (escape tName) tType) (quickQuery c query [])
          _ -> $impossible
    (TableE (TableCSV filename)) -> csvImport filename (reify (undefined :: a))
    _ -> $impossible

compareExp :: Exp a -> Exp a -> Ordering
compareExp UnitE UnitE                       = EQ
compareExp (BoolE v1) (BoolE v2)             = compare v1 v2
compareExp (CharE v1) (CharE v2)             = compare v1 v2
compareExp (IntegerE v1) (IntegerE v2)       = compare v1 v2
compareExp (DoubleE v1) (DoubleE v2)         = compare v1 v2
compareExp (TextE v1) (TextE v2)             = compare v1 v2
compareExp (PairE a1 b1) (PairE a2 b2)       = case compareExp a1 a2 of
                                                 EQ -> compareExp b1 b2
                                                 LT -> LT
                                                 GT -> GT
compareExp (ListE []) (ListE [])             = EQ
compareExp (ListE (_ : _)) (ListE [])        = GT
compareExp (ListE []) (ListE (_ : _))        = LT
compareExp (ListE (a : as)) (ListE (b : bs)) = case compareExp a b of
                                                 EQ -> compareExp (ListE as) (ListE bs)
                                                 LT -> LT
                                                 GT -> GT
compareExp _ _ = $impossible

equExp :: Exp a -> Exp a -> Bool
equExp a b = case compareExp a b of
              EQ -> True
              _  -> False

ltExp :: Exp a -> Exp a -> Bool
ltExp a b = case compareExp a b of
              LT -> True
              _  -> False

lteExp :: Exp a -> Exp a -> Bool
lteExp a b = case compareExp a b of
               GT -> False
               _  -> True

gteExp :: Exp a -> Exp a -> Bool
gteExp a b = case compareExp a b of
               LT -> False
               _  -> True

gtExp :: Exp a -> Exp a -> Bool
gtExp a b = case compareExp a b of
               GT -> True
               _  -> False

escape :: String -> String
escape []                  = []
escape (c : cs) | c == '"' = '\\' : '"' : escape cs
escape (c : cs)            =          c : escape cs

-- Pattern matching as provided by the SQL LIKE construct
matchPat :: T.Text -> T.Text -> Bool
matchPat = undefined

-- | Read SQL values into 'Norm' values
sqlToExpWithType :: (Reify a)
                 => String  -- ^ Table name, used to generate more informative error messages
                 -> Type a
                 -> [[SqlValue]]
                 -> Exp [a]
sqlToExpWithType tName ty = ListE . map (sqlValueToNorm ty)
  where
    sqlValueToNorm :: Type a -> [SqlValue] -> Exp a
    sqlValueToNorm (PairT t1 t2) s = let v1 = sqlValueToNorm t1 $ take (sizeOfType t1) s
                                         v2 = sqlValueToNorm t2 $ drop (sizeOfType t1) s
                                      in PairE v1 v2
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

convert :: SqlValue -> Type a -> Exp a
convert SqlNull         UnitT    = UnitE
convert (SqlInteger i)  IntegerT = IntegerE i
convert (SqlInt32 i)    IntegerT = IntegerE $ fromIntegral i
convert (SqlInt64 i)    IntegerT = IntegerE $ fromIntegral i
convert (SqlWord32 i)   IntegerT = IntegerE $ fromIntegral i
convert (SqlWord64 i)   IntegerT = IntegerE $ fromIntegral i
convert (SqlDouble d)  DoubleT  = DoubleE d
convert (SqlRational d) DoubleT = DoubleE $ fromRational d
convert (SqlInteger d)  DoubleT = DoubleE $ fromIntegral d
convert (SqlInt32 d)    DoubleT = DoubleE $ fromIntegral d
convert (SqlInt64 d)    DoubleT = DoubleE $ fromIntegral d
convert (SqlWord32 d)   DoubleT = DoubleE $ fromIntegral d
convert (SqlWord64 d)   DoubleT = DoubleE $ fromIntegral d
convert (SqlBool b) BoolT       = BoolE b
convert (SqlInteger i) BoolT    = BoolE (i /= 0)
convert (SqlInt32 i)   BoolT    = BoolE (i /= 0)
convert (SqlInt64 i)   BoolT    = BoolE (i /= 0)
convert (SqlWord32 i)  BoolT    = BoolE (i /= 0)
convert (SqlWord64 i)  BoolT    = BoolE (i /= 0) 
convert (SqlChar c) CharT       = CharE c
convert (SqlString (c:_)) CharT = CharE c
convert (SqlByteString c) CharT = CharE (head $ T.unpack $ T.decodeUtf8 c)
convert (SqlString t) TextT     = TextE (T.pack t) 
convert (SqlByteString s) TextT = TextE (T.decodeUtf8 s)
convert sql                 _   = error $ "Unsupported SqlValue: "  ++ show sql

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
