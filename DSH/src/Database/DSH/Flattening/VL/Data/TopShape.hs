module Database.DSH.Flattening.VL.Data.TopShape where

import Database.Algebra.Dag.Common

import Database.DSH.Flattening.VL.Data.DBVector

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
   
isOuterMost :: AlgNode -> TopShape -> Bool
isOuterMost n (ValueVector (DBV n' _) _) = n == n'
isOuterMost n (PrimVal (DBP n' _) _)     = n == n'
                                        
