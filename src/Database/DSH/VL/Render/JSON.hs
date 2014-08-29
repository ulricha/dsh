{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VL.Render.JSON(serializePlan, deserializePlan, planToFile, planFromFile) where

import           Control.Monad
import qualified Data.IntMap                 as M
import           Data.List.NonEmpty          (NonEmpty (..))
import           GHC.Generics                (Generic)

import           Data.Aeson                  (FromJSON, ToJSON, decode, encode,
                                              parseJSON, toJSON)
import qualified Data.ByteString.Lazy.Char8  as BL

import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang    as L
import           Database.DSH.VL.Lang

instance ToJSON TerOp where
instance ToJSON BinOp where
instance ToJSON UnOp where
instance ToJSON NullOp where
instance ToJSON VLVal where
instance ToJSON RowType where
instance ToJSON Expr where
instance ToJSON AggrFun where
instance ToJSON WinFun where
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
instance ToJSON FrameSpec where
instance ToJSON a => ToJSON (NonEmpty a) where
    toJSON (n :| nl) = toJSON (n, nl)


instance FromJSON TerOp where
instance FromJSON BinOp where
instance FromJSON UnOp where
instance FromJSON NullOp where
instance FromJSON VLVal where
instance FromJSON RowType where
instance FromJSON Expr where
instance FromJSON AggrFun where
instance FromJSON WinFun where
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
instance FromJSON FrameSpec where
instance FromJSON a => FromJSON (NonEmpty a) where
    parseJSON doc = parseJSON doc >>= \(n, nl) -> return $ n :| nl

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
