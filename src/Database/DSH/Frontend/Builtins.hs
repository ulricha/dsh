{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Definition of (typed) DSH builtins
module Database.DSH.Frontend.Builtins
    ( Fun(..)
    , TupElem(..)
    ) where

import           Data.Text                        (Text)
import           Data.Time.Calendar               (Day)

import           Database.DSH.Frontend.TupleTypes

-- Splice in the type for tuple element accessors
$(mkTupElemType 16)

data Fun a b where
    Not             :: Fun Bool Bool
    IntegerToDouble :: Fun Integer Double
    And             :: Fun [Bool] Bool
    Or              :: Fun [Bool] Bool
    Concat          :: Fun [[a]] [a]
    Head            :: Fun [a] a
    Tail            :: Fun [a] [a]
    Init            :: Fun [a] [a]
    Last            :: Fun [a] a
    Null            :: Fun [a] Bool
    Length          :: Fun [a] Integer
    Guard           :: Fun Bool [()]
    Reverse         :: Fun [a] [a]
    Number          :: Fun [a] [(a, Integer)]
    Fst             :: Fun (a,b) a
    Snd             :: Fun (a,b) b
    Sum             :: Fun [a] a
    Avg             :: Fun [a] Double
    Maximum         :: Fun [a] a
    Minimum         :: Fun [a] a
    Nub             :: Fun [a] [a]
    Append          :: Fun ([a], [a]) [a]
    Add             :: Fun (a,a) a
    Mul             :: Fun (a,a) a
    Sub             :: Fun (a,a) a
    Div             :: Fun (a,a) a
    Mod             :: Fun (Integer,Integer) Integer
    Lt              :: Fun (a,a) Bool
    Lte             :: Fun (a,a) Bool
    Equ             :: Fun (a,a) Bool
    NEq             :: Fun (a,a) Bool
    Gte             :: Fun (a,a) Bool
    Gt              :: Fun (a,a) Bool
    Conj            :: Fun (Bool,Bool) Bool
    Disj            :: Fun (Bool,Bool) Bool
    Cons            :: Fun (a,[a]) [a]
    Index           :: Fun ([a],Integer) a
    Zip             :: Fun ([a],[b]) [(a,b)]
    Map             :: Fun (a -> b,[a]) [b]
    ConcatMap       :: Fun (a -> [b],[a]) [b]
    Filter          :: Fun (a -> Bool,[a]) [a]
    GroupWithKey    :: Fun (a -> b,[a]) [(b, [a])]
    SortWith        :: Fun (a -> b,[a]) [a]
    Cond            :: Fun (Bool,a,a) a
    Like            :: Fun (Text,Text) Bool
    SubString       :: Integer -> Integer -> Fun Text Text
    Transpose       :: Fun [[a]] [[a]]
    Reshape         :: Integer -> Fun [a] [[a]]
    Sin             :: Fun Double Double
    Cos             :: Fun Double Double
    Tan             :: Fun Double Double
    Sqrt            :: Fun Double Double
    Exp             :: Fun Double Double
    Log             :: Fun Double Double
    ASin            :: Fun Double Double
    ACos            :: Fun Double Double
    ATan            :: Fun Double Double
    AddDays         :: Fun (Integer, Day) Day
    DiffDays        :: Fun (Day, Day) Integer
    DayDay          :: Fun Day Integer
    DayMonth        :: Fun Day Integer
    DayYear         :: Fun Day Integer
    TupElem         :: TupElem a b -> Fun a b
