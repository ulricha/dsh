{-# LANGUAGE DeriveGeneric #-}

module Database.DSH.VL.Render.JSON(serializePlan, deserializePlan, planToFile, planFromFile) where

import GHC.Generics(Generic)
import qualified Data.IntMap as M
import Control.Monad

import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Aeson (ToJSON, FromJSON, encode, decode)

import Database.DSH.Common.Data.Op
import Database.Algebra.Dag.Common
import Database.DSH.VL.Lang

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
instance ToJSON ScalarBinOp where
instance ToJSON ScalarUnOp where
instance ToJSON Empty where

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
instance FromJSON ScalarBinOp where
instance FromJSON ScalarUnOp where
instance FromJSON Empty where

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
