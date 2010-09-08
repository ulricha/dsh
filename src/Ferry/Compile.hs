{-# LANGUAGE ScopedTypeVariables #-}
module Ferry.Compile where
    
import Ferry.Pathfinder
import Ferry.Data

import qualified Data.Map as M
import Data.Maybe (fromJust)
import Control.Monad.Reader

import Text.XML.HaXml as X

import Database.HDBC

newtype AlgebraXML a = Algebra String

newtype SQLXML a = SQL String
 deriving Show
 
newtype QueryBundle a = Bundle [(Int, (String, [(String, Maybe Int)], Maybe Int, Maybe Int))]
 
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
        extractQuery c@(CElem (X.Elem n attrs cs) _) = let qId = fromJust $ fmap attrToInt $ lookup "id" attrs
                                                           rId = fmap attrToInt $ lookup "idref" attrs
                                                           cId = fmap attrToInt $ lookup "colref" attrs
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
        process (CElem (X.Elem _ attrs _) _) = let name = fromJust $ fmap attrToString $ lookup "name" attrs
                                                   pos = fmap attrToInt $ lookup "position" attrs
                                                in (name, pos)
        
runSQL :: forall a. forall conn. (QA a, IConnection conn) => conn -> QueryBundle a -> IO Norm
runSQL c (Bundle queries) = do
                             results <- mapM (runQuery c) queries
                             let refMap = foldr buildRefMap M.empty results
                             let ty = reify (undefined :: a)
                             return undefined
                             
type QueryR = Reader [(Int, ([[SqlValue]], [(String, Maybe Int)], Maybe Int, Maybe Int))]

getResults :: Int -> QueryR ([[SqlValue]], [(String, Maybe Int)], Maybe Int, Maybe Int)
getResults i = do
                env <- ask
                return $ fromJust $ lookup i env 

processResults :: Int -> Type -> QueryR [(Int, Norm)]
processResults i BoolT = do
                            (v, schema, t, c) <- getResults i
                            let partedVals = partByIter v
                            return undefined
                            
    
partByIter :: [[SqlValue]] -> [(Int, [[SqlValue]])]
partByIter v = M.toList $ foldr iterMap M.empty v

iterMap :: [SqlValue] -> M.Map Int [[SqlValue]] -> M.Map Int [[SqlValue]]
iterMap (x:xs) m = let iter = ((fromSql x)::Int)
                       vals = case M.lookup iter m of
                                    Just x  -> x
                                    Nothing -> []
                    in M.insert iter (xs:vals) m
                    
                          

{-
  UnitT
| BoolT
| CharT
| IntegerT
| DoubleT
| TupleT Type Type
| ListT Type
| ArrowT Type Type
-} 
    
runQuery :: IConnection conn => conn -> (Int, (String, [(String, Maybe Int)], Maybe Int, Maybe Int)) -> IO (Int, ([[SqlValue]], [(String, Maybe Int)], Maybe Int, Maybe Int))
runQuery c (qId, (query, schema, rId, cId)) = do
                                                res <- quickQuery' c query []
                                                return (qId, (res, schema, rId, cId))

buildRefMap :: (Int, ([[SqlValue]], [(String, Maybe Int)], Maybe Int, Maybe Int)) -> M.Map (Int, Int) (Int, [[SqlValue]], [(String, Maybe Int)]) -> M.Map (Int, Int) (Int, [[SqlValue]], [(String, Maybe Int)])
buildRefMap (q, (r, s, (Just t), (Just c))) m = M.insert (t, c) (q, r, s) m
buildRefMap _ m = m

