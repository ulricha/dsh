module Ferry.Compile where
    
import Ferry.Pathfinder

import qualified Data.Map as M
import Data.Maybe (fromJust)

import Text.XML.HaXml

data AlgebraXML a = Algebra String

data SQLXML a = SQL String
 deriving Show
 
type SQLTree = M.Map Int (String, [(String, Int)], Maybe (Int, Int))

algToSQL :: AlgebraXML a -> IO (SQLXML a)
algToSQL (Algebra s) = do
                         r <- compileFerryOpt s OutputSql Nothing 
                         case r of
                            (Right sql) -> return $ SQL sql
                            (Left err) -> error $ "Pathfinder compilation for input: \n"
                                                    ++ s ++ "\n failed with error: \n"
                                                    ++ err

-- extractSQL :: SQLXML a -> [String]
extractSQL (SQL x) = let (Document _ _ r _) = xmlParse "query" x
                      in map extractQuery $ (deep $ tag "query_plan") (CElem r undefined)
    where
        extractQuery c@(CElem (Elem n attrs cs) _) = let qId = fromJust $ fmap attrToInt $ lookup "id" attrs
                                                         rId = fmap attrToInt $ lookup "idref" attrs
                                                         cId = fmap attrToInt $ lookup "colref" attrs
                                                         query = extractCData $  head $ concatMap children $ deep (tag "query") c
                                                      in (qId, query, rId, cId)
        attrToInt :: AttValue -> Int
        attrToInt (AttValue [(Left i)]) = read i
        extractCData :: Content i -> String
        extractCData (CString _ d _) = d
    
            
