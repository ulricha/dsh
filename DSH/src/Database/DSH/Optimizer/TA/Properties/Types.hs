module Database.DSH.Optimizer.TA.Properties.Types where

import qualified Data.Set.Monad as S

import Database.Algebra.Pathfinder.Data.Algebra

data TopDownProps = TDProps { icolsProp :: S.Set AttrName }

instance Show TopDownProps where
    show ps = show $ S.toList (icolsProp ps)

-- FIXME: unite with Database.Algebra.Pathfinder....Data.Algebra.Key
type PKey = S.Set AttrName

-- | Signal if an operator produces exactly one or zero tuples, respectively.
type Card1 = Bool
type Empty = Bool

data BottomUpProps = BUProps { colsProp  :: S.Set AttrName 
     		     	     , keysProp  :: S.Set PKey
                             , card1Prop :: Card1
                             , emptyProp :: Empty
     		     	     } deriving (Show)
