{-# LANGUAGE ScopedTypeVariables, TemplateHaskell #-}
module Ferry.Compile where
    
import Ferry.Pathfinder
import Ferry.Data
import Ferry.Impossible

import qualified Data.Map as M
import Data.Maybe (fromJust)
import Control.Monad.Reader

import Text.XML.HaXml as X

import Database.HDBC
import Data.Convertible.Base

newtype AlgebraXML a = Algebra String

newtype SQLXML a = SQL String
 deriving Show
 
newtype QueryBundle a = Bundle [(Int, (String, [(String, Maybe Int)], Maybe Int, Maybe Int))]

executePlan :: forall a. forall conn. (QA a, IConnection conn) => conn -> AlgebraXML a -> IO Norm
executePlan c p = do 
                        sql <- algToSQL p
                        let plan = extractSQL sql
                        runSQL c plan
 
algToSQL :: AlgebraXML a -> IO (SQLXML a)
algToSQL (Algebra s) = do
                         r <- compileFerryOpt s OutputSql Nothing 
                         case r of
                            (Right sql) -> return $ SQL sql
                            (Left err) -> error $ "Pathfinder compilation for input: \n"
                                                    ++ s ++ "\n failed with error: \n"
                                                    ++ err

extractSQL :: SQLXML a -> QueryBundle a 
extractSQL (SQL x) = let (Document _ _ r _) = xmlParse "query" x
                      in Bundle $ map extractQuery $ (deep $ tag "query_plan") (CElem r undefined)
    where
        extractQuery c@(CElem (X.Elem n attrs cs) _) = let qId = case fmap attrToInt $ lookup "id" attrs of
                                                                    Just x -> x
                                                                    Nothing -> $impossible
                                                           rId = fmap attrToInt $ lookup "idref" attrs
                                                           cId = fmap ((1+) . attrToInt) $ lookup "colref" attrs
                                                           query = extractCData $  head $ concatMap children $ deep (tag "query") c
                                                           schema = map process $ concatMap children $ deep (tag "schema") c
                                                        in (qId, (query, schema, rId, cId))
        attrToInt :: AttValue -> Int
        attrToInt (AttValue [(Left i)]) = read i
        attrToString :: AttValue -> String
        attrToString (AttValue [(Left i)]) = i
        extractCData :: Content i -> String
        extractCData (CString _ d _) = d
        process :: Content i -> (String, Maybe Int)
        process (CElem (X.Elem _ attrs _) _) = let name = case fmap attrToString $ lookup "name" attrs of
                                                                    Just x -> x
                                                                    Nothing -> $impossible
                                                   pos = fmap attrToInt $ lookup "position" attrs
                                                in (name, pos)
        
runSQL :: forall a. forall conn. (QA a, IConnection conn) => conn -> QueryBundle a -> IO Norm
runSQL c (Bundle queries) = do
                             results <- mapM (runQuery c) queries
                             let (queryMap, valueMap) = foldr buildRefMap ([],[]) results
                             let ty = reify (undefined :: a)
                             let results = runReader (processResults 0 ty) (queryMap, valueMap) 
                             return $ snd $ head results
                             
type QueryR = Reader ([((Int, Int), Int)] ,[(Int, ([[SqlValue]]))])


getResults :: Int -> QueryR [[SqlValue]]
getResults i = do
                env <- ask
                return $ case lookup i $ snd env of
                              Just x -> x
                              Nothing -> $impossible
                
findQuery :: (Int, Int) -> QueryR Int
findQuery i = do
                env <- ask
                return $ fromJust $ lookup i $ fst env

processResults :: Int -> Type -> QueryR [(Int, Norm)]
processResults i (ListT t1) = do
                                v <- getResults i
                                let partedVals = partByIter v
                                mapM (\(it, vals) -> do
                                                      v1 <- processResults' i 1 vals t1
                                                      return (it, ListN v1)) partedVals
processResults i t = do
                        v <- getResults i
                        let partedVals = partByIter v
                        mapM (\(it, vals) -> do
                                              v1 <- processResults' i 1 vals t
                                              return (it, head v1)) partedVals

                            
processResults' :: Int -> Int -> [[SqlValue]] -> Type -> QueryR [Norm]
processResults' _ _ vals BoolT = return $ map (\[val1] -> BoolN $ convert val1) vals
processResults' _ _ vals UnitT = return $ map (\[_] -> UnitN) vals
processResults' _ _ vals IntegerT = return $ map (\[val1] -> IntegerN $ convert val1) vals
processResults' _ _ vals DoubleT = return $ map (\[val1] -> DoubleN $ convert val1) vals
processResults' q c vals (TupleT t1 t2) = mapM (\(val1:vs) -> do
                                                                v1 <- processResults' q c [[val1]] t1
                                                                v2 <- processResults' q (c + 1) [vs] t2
                                                                return $ TupleN (head v1) (head v2)) vals
processResults' q c vals (ListT t) = do
                                        nestQ <- findQuery (q, c)
                                        list <- processResults nestQ t
                                        return undefined
                                        
                            
partByIter :: [[SqlValue]] -> [(Int, [[SqlValue]])]
partByIter v = M.toList $ foldr iterMap M.empty v

iterMap :: [SqlValue] -> M.Map Int [[SqlValue]] -> M.Map Int [[SqlValue]]
iterMap (x:xs) m = let iter = ((fromSql x)::Int)
                       vals = case M.lookup iter m of
                                    Just x  -> x
                                    Nothing -> []
                    in M.insert iter (xs:vals) m
                    
runQuery :: IConnection conn => conn -> (Int, (String, [(String, Maybe Int)], Maybe Int, Maybe Int)) -> IO (Int, ([[SqlValue]], [(String, Maybe Int)], Maybe Int, Maybe Int))
runQuery c (qId, (query, schema, rId, cId)) = do
                                                res <- quickQuery' c query []
                                                return (qId, (res, schema, rId, cId))

buildRefMap :: (Int, ([[SqlValue]], [(String, Maybe Int)], Maybe Int, Maybe Int)) -> ([((Int, Int), Int)] ,[(Int, [[SqlValue]])]) -> ([((Int, Int), Int)] ,[(Int, ([[SqlValue]]))])
buildRefMap (q, (r, _, (Just t), (Just c))) (qm, rm) = (((t, c), q):qm, (q, r):rm)
buildRefMap (q, (r, _, _, _)) (qm, rm) = (qm, (q,r):rm)

