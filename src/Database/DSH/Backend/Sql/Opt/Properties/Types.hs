{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

module Database.DSH.Backend.Sql.Opt.Properties.Types where

import qualified Data.Set.Monad              as S
import           Database.Algebra.Table.Lang
import           Database.DSH.Impossible

----------------------------------------------------------------------------
-- Property types

data TopDownProps = TDProps { pICols :: S.Set Attr
                            , pUse   :: S.Set Attr
                            }

instance Show TopDownProps where
    show ps = show $ S.toList (pICols ps)

-- FIXME: unite with Database.Algebra.Pathfinder....Data.Algebra.Key
type PKey = S.Set Attr

-- | Signal if an operator produces exactly one or zero tuples, respectively.
type Card1 = Bool
type Empty = Bool

type Orders = [(Attr, [Attr])]

type ConstCol = (Attr, AVal)

data BottomUpProps = BUProps { pCols  :: S.Set TypedAttr
     		     	     , pKeys  :: S.Set PKey
                             , pCard1 :: Card1
                             , pEmpty :: Empty
                             , pOrder :: Orders
                             , pConst :: [ConstCol]
     		     	     } deriving (Show)

data AllProps = AllProps { bu :: BottomUpProps, td :: TopDownProps } deriving (Show)

----------------------------------------------------------------------------
-- Utility functions on properties

typeOf :: Attr -> S.Set TypedAttr -> ATy
typeOf k s =
    case S.toList $ [ b | (a, b) <- s, k == a ] of
        [b] -> b
        _   -> $impossible
