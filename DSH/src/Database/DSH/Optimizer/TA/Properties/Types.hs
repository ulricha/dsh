module Database.DSH.Optimizer.TA.Properties.Types where

import qualified Data.Set.Monad as S

import Database.Algebra.Pathfinder.Data.Algebra

data TopDownProps = TDProps { icolsProp :: S.Set AttrName }

instance Show TopDownProps where
    show ps = show $ S.toList (icolsProp ps)

data BottomUpProps = BUProps { colsProp :: S.Set AttrName } deriving (Show)
