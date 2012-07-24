module Optimizer.VL.Properties.Types where

data VectorProp a = VProp a
                  | VPropPair a a
                  | VPropTriple a a a
                    deriving Show
                    
data Schema = ValueVector Int
            | AtomicVector Int
            | DescrVector
            | RenameVector
            | PropVector
              deriving Show
                       
type VectorSchema = VectorProp Schema

data BottomUpProps = BUProps { emptyProp :: Bool 
                             , cardOneProp :: Bool 
                             , vectorSchemaProp :: VectorSchema } deriving (Show)
