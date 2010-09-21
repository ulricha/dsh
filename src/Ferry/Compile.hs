{-# LANGUAGE ScopedTypeVariables, TemplateHaskell, ParallelListComp #-}
module Ferry.Compile where
    
import Ferry.Pathfinder
import Ferry.Data
import Ferry.Impossible

import qualified Data.Map as M
import Data.Maybe (fromJust, isNothing, isJust)
import Data.List (sortBy)
import Control.Monad.Reader

import qualified Text.XML.HaXml as X
import Text.XML.HaXml (Content(..), AttValue(..), tag, deep, children, xmlParse, Document(..))

import Database.HDBC
import Data.Convertible.Base

newtype AlgebraXML a = Algebra String

newtype SQLXML a = SQL String
 deriving Show
 
newtype QueryBundle a = Bundle [(Int, (String, SchemaInfo, Maybe Int, Maybe Int))]

data SchemaInfo = SchemaInfo {iterN :: String, items :: [(String, Int)]}

data ResultInfo = ResultInfo {iterR :: Int, resCols :: [(String, Int)]}
 deriving Show

executePlan :: forall a. forall conn. (QA a, IConnection conn) => conn -> AlgebraXML a -> IO Norm
executePlan c p = do 
                        sql@(SQL s) <- algToSQL p
                        runSQL c $ extractSQL sql
 
algToSQL :: AlgebraXML a -> IO (SQLXML a)
algToSQL (Algebra s) = do
                         r <- compileFerryOpt s OutputSql Nothing 
                         case r of
                            (Right sql) -> return $ SQL sql
                            (Left err) -> error $ "Pathfinder compilation for input: \n"
                                                    ++ s ++ "\n failed with error: \n"
                                                    ++ err

extractSQL :: SQLXML a -> QueryBundle a 
extractSQL (SQL q) = let (Document _ _ r _) = xmlParse "query" q
                      in Bundle $ map extractQuery $ (deep $ tag "query_plan") (CElem r $impossible)
    where
        extractQuery c@(CElem (X.Elem n attrs cs) _) = let qId = case fmap attrToInt $ lookup "id" attrs of
                                                                    Just x -> x
                                                                    Nothing -> $impossible
                                                           rId = fmap attrToInt $ lookup "idref" attrs
                                                           cId = fmap attrToInt $ lookup "colref" attrs
                                                           query = extractCData $  head $ concatMap children $ deep (tag "query") c
                                                           schema = toSchemeInf $ map process $ concatMap (\x -> deep (tag "column") x) $ deep (tag "schema") c
                                                        in (qId, (query, schema, rId, cId))
        extractQuery _ = $impossible
        attrToInt :: AttValue -> Int
        attrToInt (AttValue [(Left i)]) = read i
        attrToInt _ = $impossible
        attrToString :: AttValue -> String
        attrToString (AttValue [(Left i)]) = i
        attrToString _ = $impossible
        extractCData :: Content i -> String
        extractCData (CString _ d _) = d
        extractCData _ = $impossible
        toSchemeInf :: [(String, Maybe Int)] -> SchemaInfo
        toSchemeInf results = let iterName = fst $ head $ filter (\(_, p) -> isNothing p) results
                                  cols = map (\(n, v) -> (n, fromJust v)) $ filter (\(_, p) -> isJust p) results
                               in SchemaInfo iterName cols
        process :: Content i -> (String, Maybe Int)
        process (CElem (X.Elem _ attrs _) _) = let name = fromJust $ fmap attrToString $ lookup "name" attrs 
                                                   pos = fmap attrToInt $ lookup "position" attrs
                                                in (name, pos)
        process _ = $impossible
        
runSQL :: forall a. forall conn. (QA a, IConnection conn) => conn -> QueryBundle a -> IO Norm
runSQL c (Bundle queries) = do
                             results <- mapM (runQuery c) queries
                             let (queryMap, valueMap) = foldr buildRefMap ([],[]) results
                             let ty = reify (undefined :: a)
                             let results' = runReader (processResults 0 ty) (queryMap, valueMap) 
                             return $ snd $ head results'
                             
type QueryR = Reader ([((Int, Int), Int)] ,[(Int, ([[SqlValue]], ResultInfo))])


getResults :: Int -> QueryR [[SqlValue]] 
getResults i = do
                env <- ask
                return $ case lookup i $ snd env of
                              Just x -> fst x
                              Nothing -> $impossible

getIterCol :: Int -> QueryR Int
getIterCol i = do
                env <- ask
                return $ case lookup i $ snd env of
                            Just x -> iterR $ snd x
                            Nothing -> $impossible
                            
getColResPos :: Int -> Int -> QueryR Int
getColResPos q i = do
                    env <- ask
                    return $ case lookup q $ snd env of
                                Just (_, ResultInfo _ x) -> snd (x !! i)
                                Nothing -> $impossible
                
findQuery :: (Int, Int) -> QueryR Int
findQuery (q, c) = do
                    env <- ask
                    return $ (\x -> case x of
                                  Just x' -> x'
                                  Nothing -> error $ show $ fst env) $ lookup (q, c + 1) $ fst env

processResults :: Int -> Type -> QueryR [(Int, Norm)]
processResults i ty@(ListT t1) = do
                                v <- getResults i
                                itC <- getIterCol i
                                let partedVals = partByIter itC v
                                mapM (\(it, vals) -> do
                                                        v1 <- processResults' i 0 vals t1
                                                        return (it, ListN v1 ty)) partedVals
processResults i t = do
                        v <- getResults i
                        itC <- getIterCol i
                        let partedVals = partByIter itC v
                        mapM (\(it, vals) -> do
                                              v1 <- processResults' i 0 vals t
                                              return (it, head v1)) partedVals

                            
processResults' :: Int -> Int -> [[SqlValue]] -> Type -> QueryR [Norm]
processResults' q c vals BoolT = do
                                    i <- getColResPos q c
                                    return $ map (\val -> flip BoolN BoolT $ convert $ val !! i) vals
processResults' _ _ vals UnitT = return $ map (\_ -> UnitN UnitT) vals
processResults' _ _ _    CharT = $impossible
processResults' q c vals TextT = do
                                    i <- getColResPos q c
                                    return $ map (\val -> flip TextN TextT $ convert $ val !! i) vals
processResults' q c vals IntegerT = do
                                     i <- getColResPos q c
                                     return $ map (\val -> flip IntegerN IntegerT $ convert $ val !! i) vals
processResults' q c vals DoubleT = do
                                    i <- getColResPos q c
                                    return $ map (\val -> flip DoubleN DoubleT $ convert $ val !! i) vals
processResults' q c vals t@(TupleT t1 t2) = do
                                            v1s <- processResults' q c vals t1 
                                            v2s <- processResults' q (c + 1) vals t2
                                            return $ [TupleN v1 v2 t | v1 <- v1s | v2 <- v2s]
processResults' q c vals t@(ListT _) = do
                                        nestQ <- findQuery (q, c)
                                        list <- processResults nestQ t
                                        i <- getColResPos q c
                                        let sur = map (\val -> (convert $ val !! i)::Int) vals 
                                        return $ map (\it' -> case lookup it' list of
                                                                Just x -> x
                                                                Nothing -> ListN [] t) sur
processResults' _ _ _ (ArrowT _ _) = $impossible 

                                        
                            
partByIter :: Int -> [[SqlValue]] -> [(Int, [[SqlValue]])]
partByIter n v = M.toList $ foldr (iterMap n) M.empty v

iterMap :: Int -> [SqlValue] -> M.Map Int [[SqlValue]] -> M.Map Int [[SqlValue]]
iterMap n xs m = let x = xs !! n
                     iter = ((fromSql x)::Int)
                     vals = case M.lookup iter m of
                                    Just vs  -> vs
                                    Nothing -> []
                  in M.insert iter (xs:vals) m

runQuery :: IConnection conn => conn -> (Int, (String, SchemaInfo, Maybe Int, Maybe Int)) -> IO (Int, ([[SqlValue]], ResultInfo, Maybe Int, Maybe Int))
runQuery c (qId, (query, schema, rId, cId)) = do
                                                sth <- prepare c query
                                                _ <- execute sth []
                                                res <- fetchAllRows' sth
                                                resDescr <- describeResult sth
                                                return (qId, (res, schemeToResult schema resDescr, rId, cId))

schemeToResult :: SchemaInfo -> [(String, SqlColDesc)] -> ResultInfo 
schemeToResult (SchemaInfo itN cols) resDescr = let ordCols = sortBy (\(_, c1) (_, c2) -> compare c1 c2) cols
                                                    resColumns = flip zip [0..] $ map (\(c, _) -> takeWhile (\a -> a /= '_') c) resDescr
                                                    itC = fromJust $ lookup itN resColumns
                                                 in ResultInfo itC $ map (\(n, _) -> (n, fromJust $ lookup n resColumns)) ordCols

buildRefMap :: (Int, ([[SqlValue]], ResultInfo, Maybe Int, Maybe Int)) -> ([((Int, Int), Int)] ,[(Int, ([[SqlValue]], ResultInfo))]) -> ([((Int, Int), Int)] ,[(Int, ([[SqlValue]], ResultInfo))])
buildRefMap (q, (r, ri, (Just t), (Just c))) (qm, rm) = (((t, c), q):qm, (q, (r, ri)):rm)
buildRefMap (q, (r, ri, _, _)) (qm, rm) = (qm, (q, (r, ri)):rm)

