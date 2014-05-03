{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VL.Render.JSON(serializePlan, deserializePlan, planToFile, planFromFile) where

import           GHC.Generics(Generic)
import qualified Data.IntMap as M
import qualified Data.List.NonEmpty as N
import           Control.Monad
import           Data.Functor

import qualified Data.ByteString.Lazy.Char8 as BL
import           Data.Aeson (ToJSON, FromJSON, toJSON, parseJSON, encode, decode)

import           Database.Algebra.Dag.Common

import           Database.DSH.Impossible
import qualified Database.DSH.Common.Lang as L
import           Database.DSH.VL.Lang

instance ToJSON TerOp where
instance ToJSON BinOp where
instance ToJSON UnOp where
instance ToJSON NullOp where
instance ToJSON Nat where
instance ToJSON VLVal where
instance ToJSON VLType where
instance ToJSON Expr2 where
instance ToJSON Expr1 where
instance ToJSON LeftCol where
instance ToJSON RightCol where
instance ToJSON AggrFun where
instance ToJSON L.Emptiness where
instance ToJSON L.BinStringOp where
instance ToJSON L.BinNumOp where
instance ToJSON L.BinRelOp where
instance ToJSON L.BinBoolOp where
instance ToJSON L.ScalarBinOp where
instance ToJSON L.UnCastOp where
instance ToJSON L.UnBoolOp where
instance ToJSON L.UnNumOp where
instance ToJSON L.ScalarUnOp where
instance ToJSON L.Key where
instance ToJSON L.ColName where
instance ToJSON L.TableHints where
instance ToJSON e => ToJSON (L.JoinConjunct e)
instance ToJSON e => ToJSON (L.JoinPredicate e)
instance ToJSON a => ToJSON (N.NonEmpty a) where
    toJSON nl = toJSON $ N.toList nl
  

instance FromJSON TerOp where
instance FromJSON BinOp where
instance FromJSON UnOp where
instance FromJSON NullOp where
instance FromJSON Nat where
instance FromJSON VLVal where
instance FromJSON VLType where
instance FromJSON Expr2 where
instance FromJSON Expr1 where
instance FromJSON LeftCol where
instance FromJSON RightCol where
instance FromJSON AggrFun where
instance FromJSON L.Emptiness where
instance FromJSON L.BinStringOp where
instance FromJSON L.BinNumOp where
instance FromJSON L.BinRelOp where
instance FromJSON L.BinBoolOp where
instance FromJSON L.ScalarBinOp where
instance FromJSON L.UnCastOp where
instance FromJSON L.UnBoolOp where
instance FromJSON L.UnNumOp where
instance FromJSON L.ScalarUnOp where
instance FromJSON L.ColName where
instance FromJSON L.Key where
instance FromJSON L.TableHints
instance FromJSON e => FromJSON (L.JoinConjunct e)
instance FromJSON e => FromJSON (L.JoinPredicate e)
instance FromJSON a => FromJSON (N.NonEmpty a) where
    parseJSON doc = fromList <$> parseJSON doc

fromList :: [a] -> N.NonEmpty a
fromList [] = $impossible
fromList (x : xs) = x N.:| xs
            

instance ToJSON Plan where
instance FromJSON Plan where
   
data Plan = Plan {tags :: [(AlgNode, [Tag])], roots :: [AlgNode], graph :: [(AlgNode, VL)]}
    deriving Generic
             
serializePlan :: (NodeMap [Tag], [AlgNode], NodeMap VL) -> BL.ByteString
serializePlan (ts, rs, g) = let tags' = M.toList ts
                                graph' = M.toList g
                             in encode $ Plan {tags = tags', roots = rs, graph = graph'}

deserializePlan :: BL.ByteString -> (NodeMap [Tag], [AlgNode], NodeMap VL)
deserializePlan s = let Just (Plan ts rs g) = decode s
                    in (M.fromList ts, rs, M.fromList g)
    
planToFile :: FilePath -> (NodeMap [Tag], [AlgNode], NodeMap VL) -> IO ()
planToFile f t = BL.writeFile f $ serializePlan t

planFromFile :: FilePath -> IO (NodeMap [Tag], [AlgNode], NodeMap VL)
planFromFile f = liftM deserializePlan $ BL.readFile f
