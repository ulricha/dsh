{-# LANGUAGE TemplateHaskell, RankNTypes #-}

module Ferry.TH
    (
      proj
    , generateProjRange
    , tuple
    , generateTupleRange
    , deriveTupleQA
    , generateDeriveTupleQARange
    , deriveTupleTA
    , generateDeriveTupleTARange
    , deriveTupleView
    , generateDeriveTupleViewRange
    ) where

import Control.Applicative

import Ferry.Data
import Ferry.Class
import Ferry.Impossible
import Language.Haskell.TH hiding (Q, TupleT, tupleT, AppE, VarE, reify)
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


--
-- * Tuple projection
--

proj' :: Int -> Int -> TH.Q [Dec]
proj' l pos
    | l < 2 || pos < 1 || pos > l = $impossible
    | otherwise = do
        let name = mkName $ "proj_" ++ show l ++ "_" ++ show pos
        t <- projT name l pos
        f <- projF name l pos
        return [t,f]

proj :: Int -> Int -> ExpQ
proj l pos = do
    p <- proj' l pos
    letE (map return p)
         (varE . mkName $ "proj_" ++ show l ++ "_" ++ show pos)

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
    concat `fmap` sequenceQ [ proj' n p | n <- reverse [from..to]
                                        , p <- reverse [1..n]
                                        ]


--
-- * Tuple creation
--

-- | Create a function to generate 'Q (a,b,c,...)' tuples of a given length
tuple' :: Int -> TH.Q [Dec]
tuple' l
    | l < 2     = $impossible
    | otherwise = do
        let name = mkName $ "tuple_" ++ show l
        t    <- tupleT name l
        f    <- tupleF name l
        return [t, f]

tuple :: Int -> ExpQ
tuple l = do
    t <- tuple' l
    letE (map return t)
         (varE . mkName $ "tuple_" ++ show l)

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
    concat `fmap` sequenceQ [ tuple' n | n <- reverse [from..to] ]


--
-- * QA instances
--

deriveTupleQA :: Int -> TH.Q [Dec]
deriveTupleQA l
    | l < 2     = $impossible
    | otherwise = pure `fmap` instanceD qaCxts
                                        qaType
                                        qaDecs

  where
    names@(a:b:rest) = [ mkName $ "a" ++ show i | i <- [1..l] ]

    qaCxts = return [ ClassP ''QA [VarT n] | n <- names ]
    qaType = conT ''QA `appT` applyChain (TH.tupleT l) (map varT names)
    qaDecs = [ reifyDec
             , fromNDec
             , toQDec
             ]

    -- The class functions:

    reifyDec    = funD 'reify [reifyClause]
    reifyClause = clause [ wildP ]
                         ( normalB [| TupleT $(listE [ [| reify (undefined :: $_n) |]
                                                     | _n <- map varT names  -- using _n here since
                                                                             -- -Wall will complain
                                                                             -- otherwise
                                                     ])
                                    |] )
                         [ ]

    fromNDec    = funD 'fromN [fromNClause]
    fromNClause = clause [ conP 'TupleN $ [varP a,varP b, listP (map varP rest) ] ]
                         ( normalB $ TH.tupE [ [| fromN $(varE n) |] | n <- names ] )
                         [ ]

    toQDec      = funD 'toQ [toQClause]
    toQClause   = clause [ tupP [ varP n | n <- names ] ]
                         ( normalB [| Q (TupleE (forget $ toQ $(varE a))
                                                (forget $ toQ $(varE b))
                                                $(listE [ [| forget $ toQ $(varE n) |] | n <- rest ]) )
                                    |] )
                         []

-- | Generate all 'QA' instances for tuples within range.
generateDeriveTupleQARange :: Int -> Int -> TH.Q [Dec]
generateDeriveTupleQARange from to =
    concat `fmap` sequenceQ [ deriveTupleQA n | n <- reverse [from..to] ]


--
-- * TA instances
--

-- Original code:
-- instance (BasicType a, BasicType b, QA a, QA b) => TA (a,b) where

deriveTupleTA :: Int -> TH.Q [Dec]
deriveTupleTA l
    | l < 2     = $impossible
    | otherwise = pure `fmap` instanceD taCxts
                                        taType
                                        taDecs

  where
    names = [ mkName $ "a" ++ show i | i <- [1..l] ]

    taCxts = return $ concat [ [ClassP ''QA [VarT n], ClassP ''BasicType [VarT n]] | n <- names ]
    taType = conT ''TA `appT` applyChain (TH.tupleT l) (map varT names)
    taDecs = []

-- | Generate all 'TA' instances for tuples within range.
generateDeriveTupleTARange :: Int -> Int -> TH.Q [Dec]
generateDeriveTupleTARange from to =
    concat `fmap` sequenceQ [ deriveTupleTA n | n <- reverse [from..to] ]


--
-- * View pattern
--


-- Original code:
-- instance (QA a,QA b) => View (Q (a,b)) (Q a, Q b) where
--   view (Q a) = (Q (AppE (VarE "proj_2_1") a), Q (AppE (VarE "proj_2_1") a))

deriveTupleView :: Int -> TH.Q [Dec]
deriveTupleView l
    | l < 2     = $impossible
    | otherwise = pure `fmap` instanceD viewCxts
                                        viewType
                                        viewDecs

  where
    names = [ mkName $ "a" ++ show i | i <- [1..l] ]

    viewCxts = return [ ClassP ''QA [VarT n] | n <- names ]
    viewType = conT ''View `appT` (conT ''Q `appT` applyChain (TH.tupleT l) (map varT names))
                           `appT` applyChain (TH.tupleT l) [ conT ''Q `appT` varT n | n <- names ]
    viewDecs = [ viewDec ]

    viewDec    = funD 'view [viewClause]
    viewClause = clause [ conP 'Q [varP a] ]
                        ( normalB $ TH.tupE [ [| Q (AppE (VarE $ "proj_" ++ show (l :: Int) ++ "_" ++ show (pos :: Int)) $(varE a)) |]
                                            | pos <- [1..l]
                                            ] )
                        []

    a = mkName "a"

-- | Generate all 'View' instances for tuples within range.
generateDeriveTupleViewRange :: Int -> Int -> TH.Q [Dec]
generateDeriveTupleViewRange from to =
    concat `fmap` sequenceQ [ deriveTupleView n | n <- reverse [from..to] ]
