{-# LANGUAGE DeriveGeneric #-}

module Database.DSH.Common.Data.QueryPlan where
       
import GHC.Generics(Generic)

import           Data.Aeson                                  (ToJSON)

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Builder
import           Database.Algebra.Dag.Common

import           Database.DSH.VL.Data.DBVector
import qualified Database.DSH.VL.Data.GraphVector as GV


data TopLayout = InColumn Int
               | Nest DVec TopLayout
               | Pair TopLayout TopLayout
               deriving (Show, Read, Generic)

data TopShape = ValueVector DVec TopLayout
              | PrimVal DVec TopLayout
              deriving (Show, Read, Generic)

instance ToJSON TopLayout where
instance ToJSON TopShape where

rootsFromTopLayout :: TopLayout -> [AlgNode]
rootsFromTopLayout (InColumn _)         = []
rootsFromTopLayout (Nest (DVec n _) lyt) = n : rootsFromTopLayout lyt
rootsFromTopLayout (Pair lyt1 lyt2)     = (rootsFromTopLayout lyt1) ++ (rootsFromTopLayout lyt2)

rootsFromTopShape :: TopShape -> [AlgNode]
rootsFromTopShape (ValueVector (DVec n _) lyt) = n : rootsFromTopLayout lyt
rootsFromTopShape (PrimVal (DVec n _) lyt)     = n : rootsFromTopLayout lyt

updateTopShape :: AlgNode -> AlgNode -> TopShape -> TopShape
updateTopShape old new shape =
  let updateDVec (DVec n cols) = DVec (if n == old then new else n) cols

      updateLayout (Nest dbv lyt)   = Nest (updateDVec dbv) (updateLayout lyt)
      updateLayout (Pair lyt1 lyt2) = Pair (updateLayout lyt1) (updateLayout lyt2)
      updateLayout l                = l

  in
   case shape of
     ValueVector dbv lyt -> ValueVector (updateDVec dbv) (updateLayout lyt)
     PrimVal dbv lyt -> PrimVal (updateDVec dbv) (updateLayout lyt)

columnsInLayout :: TopLayout -> Int
columnsInLayout (InColumn _) = 1
columnsInLayout (Nest _ _) = 0
columnsInLayout (Pair p1 p2) = columnsInLayout p1 + columnsInLayout p2

isOuterMost :: AlgNode -> TopShape -> Bool
isOuterMost n (ValueVector (DVec n' _) _) = n == n'
isOuterMost n (PrimVal (DVec n' _) _)     = n == n'

importShape :: TopShape -> GV.Shape
importShape (ValueVector (DVec n cols) lyt) = GV.ValueVector (DVec n cols) (importLayout lyt)
importShape (PrimVal (DVec n cols) lyt)     = GV.PrimVal (DVec n cols) (importLayout lyt)

importLayout :: TopLayout -> GV.Layout
importLayout (InColumn i)              = GV.InColumn i
importLayout (Nest (DVec n cols) lyt) = GV.Nest (DVec n cols) (importLayout lyt)
importLayout (Pair lyt1 lyt2)          = GV.Pair (importLayout lyt1) (importLayout lyt2)

exportShape :: GV.Shape -> TopShape
exportShape (GV.ValueVector (DVec n cols) lyt) = ValueVector (DVec n cols) (exportLayout lyt)
exportShape (GV.PrimVal (DVec n cols) lyt)     = PrimVal (DVec n cols) (exportLayout lyt)
exportShape s                                  = error $ "exportShape: impossible top-level shape " ++ (show s)

exportLayout :: GV.Layout -> TopLayout
exportLayout (GV.InColumn i)            = InColumn i
exportLayout (GV.Nest (DVec n cols) lyt) = Nest (DVec n cols) (exportLayout lyt)
exportLayout (GV.Pair lyt1 lyt2)        = Pair (exportLayout lyt1) (exportLayout lyt2)


-- | A query plan consists of a DAG over some algebra and information about the
-- shape of the query.
data QueryPlan a =
  QueryPlan { queryDag   :: AlgebraDag a
            , queryShape :: TopShape
            , queryTags  :: NodeMap [Tag]
            }

mkQueryPlan :: Operator a => AlgMap a -> TopShape -> NodeMap [Tag] -> QueryPlan a
mkQueryPlan opMap shape tagMap =
  let rs                     = rootsFromTopShape shape
      d                      = mkDag (reverseAlgMap opMap) rs
  in QueryPlan { queryDag = d, queryShape = shape, queryTags = tagMap }
