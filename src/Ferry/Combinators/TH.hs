{-# LANGUAGE TemplateHaskell, RankNTypes #-}

module Ferry.Combinators.TH
    (
      proj
    , generateProjRange
    , tuple
    , generateTupleRange
    ) where

import Control.Applicative

import Ferry.Data
import Ferry.Class
import Ferry.Impossible
import Language.Haskell.TH hiding (Q, tupleT, AppE, VarE)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax (sequenceQ)


-- Create a "a -> b -> ..." type
arrowChain :: [TypeQ] -> TypeQ
arrowChain []     = $impossible
arrowChain [a]    = a
arrowChain (a:as) = arrowT `appT` a `appT` arrowChain as

-- Apply a list of 'TypeQ's to a type constructor
applyChain :: TypeQ -> [TypeQ] -> TypeQ
applyChain t []     = t
applyChain t [n]    = t `appT` n
applyChain t (n:ns) = applyChain (t `appT` n) ns


-- * Tuple projection

proj :: Int -> Int -> TH.Q [Dec]
proj l pos
    | l < 2 || pos < 1 || pos > l = $impossible
    | otherwise = do
        let name = mkName $ "proj_" ++ show l ++ "_" ++ show pos
        t <- projT name l pos
        f <- projF name l pos
        return [t,f]

-- Type definition for 'proj'
projT :: Name -> Int -> Int -> DecQ
projT name l pos = sigD name $
    forallT [ PlainTV n | n <- names ]
            qaCxt
            theType

  where
    names   = [ mkName $ "a" ++ show i | i <- [1..l] ]
    qaCxt   = return [ ClassP ''QA [VarT n] | n <- names ]
    theType = arrowChain [ conT ''Q `appT` (applyChain (TH.tupleT l) $ map varT names)
                         , conT ''Q `appT` (map varT names !! (pos-1))
                         ]

-- Function definition for 'proj'
projF :: Name -> Int -> Int -> DecQ
projF name l pos = funD name . pure $
    clause [ conP 'Q [varP a] ]
           (normalB [| Q (AppE (VarE $ "proj_" ++ show (l :: Int) ++ "_" ++ show (pos :: Int))
                               $(varE a))
                     |])
           []

  where
    a = mkName "a"


-- | Generate "proj_X_p" functions in a given range. Only the length of the
-- tuples are necessary, all \"selectors\" are generated automatically
generateProjRange :: Int -> Int -> TH.Q [Dec]
generateProjRange from to =
    concat `fmap` sequenceQ [ proj n p | n <- reverse [from..to]
                                       , p <- reverse [1..n]
                                       ]


-- * Tuple creation

-- | Create a function to generate 'Q (a,b,c,...)' tuples of a given length
tuple :: Int -> TH.Q [Dec]
tuple l
    | l < 2     = $impossible
    | otherwise = do
        let name = mkName $ "tuple_" ++ show l
        t    <- tupleT name l
        f    <- tupleF name l
        return [t, f]

-- Function definition: Create a \"Q (a,b,c,...)\" tuple
tupleF :: Name -> Int -> DecQ
tupleF name l = funD name . pure $
    clause [ conP 'Q [varP n] | n <- names ]
           (normalB [| Q (TupleE $a $b $(listE rest)) |])
           []

  where
    names       = [ mkName $ "a" ++ show i | i <- [1..l] ]
    (a:b:rest)  = map varE names

-- Type definition for the 'tupleF' function
tupleT :: Name -> Int -> DecQ
tupleT name l = sigD name $
    forallT [ PlainTV n | n <- names ]
            qaCxt
            theType

  where
    names = [ mkName $ "a" ++ show i | i <- [1..l] ]

    qaCxt :: CxtQ
    qaCxt = return [ ClassP ''QA [VarT n] | n <- names ]

    theType :: TypeQ
    theType = arrowChain $ [ conT ''Q `appT` varT n | n <- names ]
                        ++ [ conT ''Q `appT` finalTuple ]

    -- Put all the variable names into one tuple
    finalTuple :: TypeQ
    finalTuple  = applyChain (TH.tupleT l) $ map varT names

-- | Generate "tuple_X" functions in a given range
generateTupleRange :: Int           -- ^ From
                   -> Int           -- ^ To
                   -> TH.Q [Dec]
generateTupleRange from to =
    concat `fmap` sequenceQ [ tuple n | n <- reverse [from..to] ]
