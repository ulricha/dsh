module Optimizer.VL.Properties.Types where

data BottomUpProps = BUProps { emptyProp :: Bool 
                             , cardOneProp :: Bool 
                             , widthProp :: Int } deriving (Show)
