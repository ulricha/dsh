module Database.DSH.Optimizer.TA.Properties.Types where

import qualified Data.Set.Monad as S

import Database.Algebra.Pathfinder.Data.Algebra

data TopDownProps = TDProps { pICols :: S.Set AttrName 
                            , pUse   :: S.Set AttrName
                            }

instance Show TopDownProps where
    show ps = show $ S.toList (pICols ps)

-- FIXME: unite with Database.Algebra.Pathfinder....Data.Algebra.Key
type PKey = S.Set AttrName

-- | Signal if an operator produces exactly one or zero tuples, respectively.
type Card1 = Bool
type Empty = Bool

data BottomUpProps = BUProps { pCols  :: S.Set AttrName 
     		     	     , pKeys  :: S.Set PKey
                             , pCard1 :: Card1
                             , pEmpty :: Empty
     		     	     } deriving (Show)
