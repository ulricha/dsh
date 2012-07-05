module Language.ParallelLang.VL.Render.JSON where

import Database.Algebra.Dag.Builder
import Database.Algebra.Dag.Common

import Language.ParallelLang.VL.Data.DBVector
import Language.ParallelLang.VL.Data.VectorLanguage
import Language.ParallelLang.VL.Data.GraphVector
import Language.ParallelLang.Common.Data.Type
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.FKL.Data.FKL
import Language.ParallelLang.Common.Data.Val

import qualified Data.Map as M

import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Aeson (ToJSON, encode)

instance ToJSON Plan where
instance ToJSON TerOp where
instance ToJSON BinOp where
instance ToJSON UnOp where
instance ToJSON NullOp where
instance ToJSON PVal where
instance ToJSON Type where
instance ToJSON DBV where
instance ToJSON DBP where
instance ToJSON Layout where
instance ToJSON Oper where
instance ToJSON Expr where
instance ToJSON Prim1 where
instance ToJSON Prim2 where
instance ToJSON Prim3 where
instance ToJSON Op where
instance ToJSON Val where
instance (ToJSON t, ToJSON b, ToJSON u, ToJSON n, ToJSON c) => ToJSON (Algebra t b u n c) where
    
serialisePlan :: AlgPlan VL Plan -> String
serialisePlan (m, p, _) = BL.unpack $ encode (p, M.toList $ reverseAlgMap m)


    
    