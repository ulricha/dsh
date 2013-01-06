module Database.DSH.Flattening.Common.Data.QueryPlan where

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Builder
import           Database.Algebra.Dag.Common

import           Database.DSH.Flattening.VL.Data.DBVector
import qualified Database.DSH.Flattening.VL.Data.GraphVector as GV

data TopLayout = InColumn Int
               | Nest DBV TopLayout
               | Pair TopLayout TopLayout
               deriving (Show, Read)

data TopShape = ValueVector DBV TopLayout
              | PrimVal DBP TopLayout
              deriving (Show, Read)

rootsFromTopLayout :: TopLayout -> [AlgNode]
rootsFromTopLayout (InColumn _)         = []
rootsFromTopLayout (Nest (DBV n _) lyt) = n : rootsFromTopLayout lyt
rootsFromTopLayout (Pair lyt1 lyt2)     = (rootsFromTopLayout lyt1) ++ (rootsFromTopLayout lyt2)

rootsFromTopShape :: TopShape -> [AlgNode]
rootsFromTopShape (ValueVector (DBV n _) lyt) = n : rootsFromTopLayout lyt
rootsFromTopShape (PrimVal (DBP n _) lyt)     = n : rootsFromTopLayout lyt

updateTopShape :: AlgNode -> AlgNode -> TopShape -> TopShape
updateTopShape old new shape =
  let updateDBV (DBV n cols) = DBV (if n == old then new else n) cols

      updateDBP (DBP n cols) = DBP (if n == old then new else n) cols

      updateLayout (Nest dbv lyt)   = Nest (updateDBV dbv) (updateLayout lyt)
      updateLayout (Pair lyt1 lyt2) = Pair (updateLayout lyt1) (updateLayout lyt2)
      updateLayout l                = l

  in
   case shape of
     ValueVector dbv lyt -> ValueVector (updateDBV dbv) (updateLayout lyt)
     PrimVal dbp lyt -> PrimVal (updateDBP dbp) (updateLayout lyt)

columnsInLayout :: TopLayout -> Int
columnsInLayout (InColumn _) = 1
columnsInLayout (Nest _ _) = 0
columnsInLayout (Pair p1 p2) = columnsInLayout p1 + columnsInLayout p2

isOuterMost :: AlgNode -> TopShape -> Bool
isOuterMost n (ValueVector (DBV n' _) _) = n == n'
isOuterMost n (PrimVal (DBP n' _) _)     = n == n'

importShape :: TopShape -> GV.Shape
importShape (ValueVector (DBV n cols) lyt) = GV.ValueVector (DBV n cols) (importLayout lyt)
importShape (PrimVal (DBP n cols) lyt)     = GV.PrimVal (DBP n cols) (importLayout lyt)

importLayout :: TopLayout -> GV.Layout
importLayout (InColumn i)              = GV.InColumn i
importLayout (Nest (DBV n cols) lyt) = GV.Nest (DBV n cols) (importLayout lyt)
importLayout (Pair lyt1 lyt2)          = GV.Pair (importLayout lyt1) (importLayout lyt2)

exportShape :: GV.Shape -> TopShape
exportShape (GV.ValueVector (DBV n cols) lyt) = ValueVector (DBV n cols) (exportLayout lyt)
exportShape (GV.PrimVal (DBP n cols) lyt)     = PrimVal (DBP n cols) (exportLayout lyt)
exportShape s                                  = error $ "exportShape: impossible top-level shape " ++ (show s)

exportLayout :: GV.Layout -> TopLayout
exportLayout (GV.InColumn i)            = InColumn i
exportLayout (GV.Nest (DBV n cols) lyt) = Nest (DBV n cols) (exportLayout lyt)
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
