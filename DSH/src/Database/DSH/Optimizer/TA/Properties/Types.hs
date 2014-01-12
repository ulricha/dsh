{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE MonadComprehensions #-}

module Database.DSH.Optimizer.TA.Properties.Types where

import Database.DSH.Impossible

import qualified Data.Set.Monad as S

import Database.Algebra.Pathfinder.Data.Algebra

----------------------------------------------------------------------------
-- Property types

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

type Orders = [(AttrName, [AttrName])]

data BottomUpProps = BUProps { pCols  :: S.Set TypedAttr 
     		     	     , pKeys  :: S.Set PKey
                             , pCard1 :: Card1
                             , pEmpty :: Empty
                             , pOrder :: Orders
     		     	     } deriving (Show)

data AllProps = AllProps { bu :: BottomUpProps, td :: TopDownProps } deriving (Show)
     
----------------------------------------------------------------------------
-- Utility functions on properties

typeOf :: AttrName -> S.Set TypedAttr -> ATy
typeOf k s =
    case S.toList $ [ b | (a, b) <- s, k == a ] of
        [b] -> b
        _   -> $impossible
