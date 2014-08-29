{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VL.Render.JSON(serializePlan, deserializePlan, planToFile, planFromFile) where

import           Control.Monad
import qualified Data.IntMap                 as M
import           Data.List.NonEmpty          (NonEmpty (..))
import           GHC.Generics                (Generic)

import           Data.Aeson                  (FromJSON, ToJSON, decode, encode,
                                              parseJSON, toJSON)
import           Data.Aeson.TH
import qualified Data.ByteString.Lazy.Char8  as BL

import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang    as L
import           Database.DSH.VL.Lang

data Plan = Plan { tags :: [(AlgNode, [Tag])]
                 , roots :: [AlgNode]
                 , graph :: [(AlgNode, VL)]
                 }
    deriving Generic

$(deriveJSON defaultOptions ''Plan)

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
