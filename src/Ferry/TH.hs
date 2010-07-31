{-# LANGUAGE TemplateHaskell, RankNTypes #-}

module Ferry.TH
    (
      proj
    , generateProjRange
    , tuple
    , generateTupleRange
    , deriveQA
    , generateDeriveQARange
    , deriveTA
    , generateDeriveTARange
    , deriveView
    , generateDeriveViewRange
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
           (normalB [| Q (foldr1 TupleE $(listE (a : b : rest))) |])
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

deriveQA :: Int -> TH.Q [Dec]
deriveQA l
    | l < 2     = $impossible
    | otherwise = pure `fmap` instanceD qaCxts
                                        qaType
                                        qaDecs

  where
    names@(a:b:rest) = [ mkName $ "a" ++ show i | i <- [1..l] ]

    qaCxts = return [ ClassP ''QA [VarT n] | n <- names ]
    qaType = conT ''QA `appT` applyChain (TH.tupleT l) (map varT names)
    qaDecs = [ reifyDec
             , fromNormDec
             , toNormDec
             ]

    -- The class functions:

    reifyDec    = funD 'reify [reifyClause]
    reifyClause = clause [ wildP ]
                         ( normalB [| foldr1 TupleT $(listE [ [| reify (undefined :: $_n) |]
                                                            | _n <- map varT names  -- using _n here since
                                                                             -- -Wall will complain
                                                                             -- otherwise
                                                            ])
                                    |] )
                         [ ]

    fromNormDec    = funD 'fromNorm [fromNormClause]
    fromNormClause = clause [foldr1 (\p1 p2 -> conP 'TupleN [p1,p2]) (map varP names)]
                            (normalB $ TH.tupE [ [| fromNorm $(varE n) |] | n <- names ])
                            []

    toNormDec      = funD 'toNorm [toNormClause]
    toNormClause   = clause [ tupP [ varP n | n <- names ] ]
                         ( normalB [|  (foldr1 TupleN $(listE [ [|toNorm $(varE n) |] | n <- names ]))
                                   |] )
                         []

-- | Generate all 'QA' instances for tuples within range.
generateDeriveQARange :: Int -> Int -> TH.Q [Dec]
generateDeriveQARange from to =
    concat `fmap` sequenceQ [ deriveQA n | n <- reverse [from..to] ]


--
-- * TA instances
--

-- Original code:
-- instance (BasicType a, BasicType b, QA a, QA b) => TA (a,b) where

deriveTA :: Int -> TH.Q [Dec]
deriveTA l
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
generateDeriveTARange :: Int -> Int -> TH.Q [Dec]
generateDeriveTARange from to =
    concat `fmap` sequenceQ [ deriveTA n | n <- reverse [from..to] ]


--
-- * View pattern
--


-- Original code:
-- instance (QA a,QA b) => View (Q (a,b)) (Q a, Q b) where
--   view (Q a) = (Q (AppE (VarE "proj_2_1") a), Q (AppE (VarE "proj_2_1") a))

deriveView :: Int -> TH.Q [Dec]
deriveView l
    | l < 2     = $impossible
    | otherwise = pure `fmap` instanceD viewCxts
                                        viewType
                                        viewDecs

  where
    names = [ mkName $ "a" ++ show i | i <- [1..l] ]
    a = mkName "a"    

    first  p = [| AppE (VarE "fst") $p |]
    second p = [| AppE (VarE "snd") $p |]

    viewCxts = return [ ClassP ''QA [VarT n] | n <- names ]
    viewType = conT ''View `appT` (conT ''Q `appT` applyChain (TH.tupleT l) (map varT names))
                           `appT` applyChain (TH.tupleT l) [ conT ''Q `appT` varT n | n <- names ]

    viewDecs = [ viewDec ]
    
    viewDec    = funD 'view [viewClause]
    viewClause = clause [ conP 'Q [varP a] ]
                        ( normalB $ TH.tupE [ if pos == l then [| Q $(f (varE a)) |] else [| Q $(first (f (varE a))) |]
                                            | pos <- [1..l]
                                            , let f = foldr (.) id (replicate (pos - 1) second)
                                            ])
                        []

-- | Generate all 'View' instances for tuples within range.
generateDeriveViewRange :: Int -> Int -> TH.Q [Dec]
generateDeriveViewRange from to =
    concat `fmap` sequenceQ [ deriveView n | n <- reverse [from..to] ]
