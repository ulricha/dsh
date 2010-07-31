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

    , deriveQAForRecord
    , deriveQAForRecord'
    , deriveViewForRecord
    , deriveViewForRecord'
    , deriveRecordInstances
    ) where

import Control.Applicative
import Data.List

import Ferry.Data
import Ferry.Class
import Ferry.Impossible
import Language.Haskell.TH hiding (Q, TupleT, tupleT, AppE, VarE, reify)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax (sequenceQ)


-- Create a "a -> b -> ..." type
arrowChainT :: [TypeQ] -> TypeQ
arrowChainT [] = $impossible
arrowChainT as = foldr1 (\a b -> arrowT `appT` a `appT` b) as

-- Apply a list of 'TypeQ's to a type constructor
applyChainT :: TypeQ -> [TypeQ] -> TypeQ
applyChainT t ts = foldl' appT t ts

-- Apply a list of 'Exp's to a some 'Exp'
applyChainE :: ExpQ -> [ExpQ] -> ExpQ
applyChainE e es = foldl' appE e es

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
    theType = arrowChainT [ conT ''Q `appT` (applyChainT (TH.tupleT l) $ map varT names)
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
    theType = arrowChainT $ [ conT ''Q `appT` varT n | n <- names ]
                         ++ [ conT ''Q `appT` finalTuple ]

    -- Put all the variable names into one tuple
    finalTuple :: TypeQ
    finalTuple  = applyChainT (TH.tupleT l) $ map varT names

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
    qaType = conT ''QA `appT` applyChainT (TH.tupleT l) (map varT names)
    qaDecs = [ reifyDec
             , fromNormDec
             , toNormDec
             ]

    -- The class functions:

    reifyDec    = funD 'reify [reifyClause]
    reifyClause = clause [ wildP ]
                         ( normalB [| foldr1 TupleT $(listE [ [| reify (undefined :: $_n) |]
                                                            | _n <- map varT names
                                                            ] )
                                    |] )
                         [ ]

    fromNormDec    = funD 'fromNorm [fromNormClause]
    fromNormClause = clause [foldr1 (\p1 p2 -> conP 'TupleN [p1,p2]) (map varP names)]
                            (normalB $ TH.tupE [ [| fromNorm $(varE n) |] | n <- names ])
                            []

    toNormDec    = funD 'toNorm [toNormClause]
    toNormClause = clause [ tupP [ varP n | n <- names ] ]
                          ( normalB [|  (foldr1 TupleN $(listE [ [|toNorm $(varE n) |] | n <- names ]))
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
    taType = conT ''TA `appT` applyChainT (TH.tupleT l) (map varT names)
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
    a = mkName "a"    

    first  p = [| AppE (VarE "fst") $p |]
    second p = [| AppE (VarE "snd") $p |]

    viewCxts = return [ ClassP ''QA [VarT n] | n <- names ]
    viewType = conT ''View `appT` (conT ''Q `appT` applyChainT (TH.tupleT l) (map varT names))
                           `appT` applyChainT (TH.tupleT l) [ conT ''Q `appT` varT n | n <- names ]

    viewDecs = [ viewDec ]
    
    viewDec    = funD 'view [viewClause]
    viewClause = clause [ conP 'Q [varP a] ]
                        ( normalB $ TH.tupE [ if pos == l then [| Q $(f (varE a)) |] else [| Q $(first (f (varE a))) |]
                                            | pos <- [1..l]
                                            , let f = foldr (.) id (replicate (pos - 1) second)
                                            ])
                        []

-- | Generate all 'View' instances for tuples within range.
generateDeriveTupleViewRange :: Int -> Int -> TH.Q [Dec]
generateDeriveTupleViewRange from to =
    concat `fmap` sequenceQ [ deriveTupleView n | n <- reverse [from..to] ]




--------------------------------------------------------------------------------
-- * Deriving Instances for Records
--

-- | Derive the 'QA' instance for a record definition.
deriveQAForRecord :: TH.Q [Dec] -> TH.Q [Dec]
deriveQAForRecord q = do
    d <- q
    i <- deriveQAForRecord' q
    return $ d ++ i

-- | Add 'QA' instance to a record without adding the actual data definition.
-- Usefull in combination with 'deriveQAForRecord''
deriveQAForRecord' :: TH.Q [Dec] -> TH.Q [Dec]
deriveQAForRecord' q = do
    d <- q
    mapM addInst d
  where
    addInst d@(DataD [] dName [] [RecC rName rVar@(_:_)] _) | dName == rName = do

         let rCxt  = return []
             rType = conT ''QA `appT` conT dName
             rDec  = [ reifyDec
                     , toNormDec
                     , fromNormDec
                     ]

             reifyDec    = funD 'reify [reifyClause]
             reifyClause = clause [ recP rName [] ]
                                  ( normalB $ [| foldr1 TupleT $(listE [ [| reify (undefined :: $(return _t)) |]
                                                                       | (_,_,_t) <- rVar
                                                                       ])
                                              |])
                                  []

             names = [ mkName $ "a" ++ show i | i <- [1..length rVar] ]

             fromNormDec    = funD 'fromNorm [fromNormClause]
             fromNormClause = clause [ foldr1 (\p1 p2 -> conP 'TupleN [p1,p2]) (map varP names) ]
                                     ( normalB $ (conE dName) `applyChainE` [ [| fromNorm $(varE n) |]
                                                                            | n <- names
                                                                            ]
                                     )
                                     []

             toNormDec    = funD 'toNorm [toNormClause]
             toNormClause = clause [ conP dName (map varP names) ]
                                   ( normalB [| foldr1 TupleN $(listE [ [| toNorm $(varE n) |]
                                                                      | n <- names ])
                                             |] )
                                   []

         instanceD rCxt
                   rType
                   rDec

    addInst _ = error "ferry: Invalid record definition"

-- | Derive the 'View' instance for a record definition. See
-- 'deriveQAForRecord' for an example.
deriveViewForRecord :: TH.Q [Dec] -> TH.Q [Dec]
deriveViewForRecord q = do
    d <- q
    i <- deriveViewForRecord' q
    return $ d ++ i

-- | Add 'View' instance to a record without adding the actual data definition.
-- Usefull in combination with 'deriveQAForRecord''
deriveViewForRecord' :: TH.Q [Dec] -> TH.Q [Dec]
deriveViewForRecord' q = do
    d <- q
    concat `fmap` mapM addView d
  where
    addView (DataD [] dName [] [RecC rName rVar@(_:_)] dNames) | dName == rName = do

        -- The "View" record definition

        let vName  = mkName $ nameBase dName ++ "V"
            vRec   = recC vName [ return (prefixQ n, s, makeQ t) | (n,s,t) <- rVar ]
              where prefixQ :: Name -> Name
                    prefixQ n = mkName $ "q_" ++ nameBase n

                    makeQ :: TH.Type -> TH.Type
                    makeQ t = ConT ''Q `AppT` t

            vNames = dNames

        v <- dataD (return [])
                   vName
                   []
                   [vRec]
                   vNames

        -- The instance definition

        let rCxt  = return []
            rType = conT ''View `appT` (conT ''Q `appT` conT dName)
                                `appT` (conT vName)
            rDec  = [ viewDec ]

            a      = mkName "a"

            viewDec    = funD 'view [viewClause]
            viewClause = clause [ conP 'Q [varP a] ]
                                ( normalB $ applyChainE (conE vName)
                                                        [ [| Q (AppE (VarE n) $(varE a)) |]
                                                        | n <- map (\(n,_,_) -> nameBase n) rVar
                                                        ]
                                )
                                []

        i <- instanceD rCxt
                       rType
                       rDec

        return [v,i]

    addView _ = error "ferry: Invalid record definition"


-- | Derive 'QA' and 'View' instances for record definitions
--
-- Example usage:
--
-- > $(deriveRecordInstances [d|
-- >
-- >     data User = User
-- >         { user_id    :: Int
-- >         , user_name  :: String
-- >         }
-- >
-- >   |])
deriveRecordInstances :: TH.Q [Dec] -> TH.Q [Dec]
deriveRecordInstances q = do
    d  <- q
    qa <- deriveQAForRecord' q
    v  <- deriveViewForRecord' q
    return $ d ++ qa ++ v
