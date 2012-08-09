module Optimizer.Common.Shape where

import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data(DBCol)

data DBV = DBV AlgNode [DBCol] deriving (Show, Read)

data DBP = DBP AlgNode [DBCol] deriving (Show, Read)
  
data Layout = InColumn Int
            | Nest DBV Layout
            | Pair Layout Layout
            deriving (Show, Read)
              
data Shape = ValueVector DBV Layout
           | PrimVal DBP Layout
           deriving (Show, Read)
             
rootsFromLayout :: Layout -> [AlgNode]
rootsFromLayout (InColumn _)         = []
rootsFromLayout (Nest (DBV n _) lyt) = n : rootsFromLayout lyt
rootsFromLayout (Pair lyt1 lyt2)     = (rootsFromLayout lyt1) ++ (rootsFromLayout lyt2)
                                      
rootsFromShape :: Shape -> [AlgNode]
rootsFromShape (ValueVector (DBV n _) lyt) = n : rootsFromLayout lyt
rootsFromShape (PrimVal (DBP n _) lyt)     = n : rootsFromLayout lyt
                                             
                                             
updateShape :: AlgNode -> AlgNode -> Shape -> Shape
updateShape old new shape = 
  let updateDBV (DBV n cols) = DBV (if n == old then new else n) cols

      updateDBP (DBP n cols) = DBP (if n == old then new else n) cols

      updateLayout (Nest dbv lyt)   = Nest (updateDBV dbv) (updateLayout lyt)
      updateLayout (Pair lyt1 lyt2) = Pair (updateLayout lyt1) (updateLayout lyt2)
      updateLayout l                = l

  in 
   case shape of
     ValueVector dbv lyt -> ValueVector (updateDBV dbv) (updateLayout lyt) 
     PrimVal dbp lyt -> PrimVal (updateDBP dbp) (updateLayout lyt) 
   
isOuterMost :: AlgNode -> Shape -> Bool
isOuterMost n (ValueVector (DBV n' _) _) = n == n'
isOuterMost n (PrimVal (DBP n' _) _)     = n == n'
                                        
