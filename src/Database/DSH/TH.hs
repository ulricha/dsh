{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}

module Database.DSH.TH
    (
      deriveTupleQA
    , generateDeriveTupleQARange
    , deriveTupleTA
    , generateDeriveTupleTARange
    , deriveTupleView
    , generateDeriveTupleViewRange

    , deriveQAForRecord
    , deriveQAForRecord'
    , deriveViewForRecord
    , deriveViewForRecord'
    , deriveTAForRecord
    , deriveTAForRecord'

    , createTableRepresentation
    , createTableRepresentation'
    ) where


import Database.DSH.Data
import Database.DSH.Impossible

import Control.Applicative
import Control.Monad
import Data.Convertible
import Data.List
import Database.HDBC
import Data.Text (Text)
import Data.Time (UTCTime)
import GHC.Exts

import Language.Haskell.TH hiding (Q, TupleT, tupleT, AppE, VarE, reify, Type, ListT)
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

applyChainTupleP :: [PatQ] -> PatQ
applyChainTupleP = foldr1 (\p1 p2 -> conP 'TupleN [p1,p2,wildP])

applyChainTupleE :: Name -> [ExpQ] -> ExpQ
applyChainTupleE n = foldr1 (\e1 e2 -> appE (appE (conE n) e1) e2)


-- Some Applicative magic :)
instance Applicative TH.Q where
    pure  = return
    (<*>) = ap


--------------------------------------------------------------------------------
-- * QA instances
--

-- Original Code
-- instance (QA a,QA b) => QA (a,b) where
--   reify _ = TupleT (reify (undefined :: a)) (reify (undefined :: b))
--   toNorm (a,b) = TupleN (toNorm a) (toNorm b) (reify (a,b))
--   fromNorm (TupleN a b (TupleT _ _)) = (fromNorm a,fromNorm b)
--   fromNorm _ = $impossible

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
                         ( normalB $ applyChainTupleE 'TupleT [ [| reify (undefined :: $_n) |] | _n <- map varT names ] )
                         []

    fromNormDec    = funD 'fromNorm [fromNormClause, clause [TH.wildP] (normalB [| $impossible |]) [] ]
    fromNormClause = clause [applyChainTupleP (map varP names)]
                            (normalB $ TH.tupE [ [| fromNorm $(varE n) |] | n <- names ])
                            []

    toNormDec    = funD 'toNorm [toNormClause]
    toNormClause = clause [ toNormClausePattern ] (normalB $ fst $ toNormClauseBody $ [ varE n | n <- names ]) []

    toNormClausePattern = tupP [ varP n | n <- names ]

    toNormClauseBody [a1,b1] =
      let t1 = [| TupleT (reify $a1) (reify $b1) |]
          e1 = [| TupleN (toNorm $a1) (toNorm $b1) ($t1) |]
      in  (e1,t1)
    toNormClauseBody (a1 : as1) =
      let (e1,t1) = toNormClauseBody as1
          t2 = [| TupleT (reify $a1) ($t1) |]
          e2 = [| TupleN (toNorm $a1) ($e1) ($t2) |]
      in  (e2,t2)
    toNormClauseBody _ = $impossible


-- | Generate all 'QA' instances for tuples within range.
generateDeriveTupleQARange :: Int -> Int -> TH.Q [Dec]
generateDeriveTupleQARange from to =
    concat `fmap` sequenceQ [ deriveTupleQA n | n <- reverse [from..to] ]


--------------------------------------------------------------------------------
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


--------------------------------------------------------------------------------
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

    first  p = [| AppE1 Fst $p (typeTupleFst (typeExp $p)) |]
    second p = [| AppE1 Snd $p (typeTupleSnd (typeExp $p)) |]

    viewCxts = return [ ClassP ''QA [VarT n] | n <- names ]
    viewType = conT ''View `appT` (conT ''Q `appT` applyChainT (TH.tupleT l) (map varT names))
                           `appT` applyChainT (TH.tupleT l) [ conT ''Q `appT` varT n | n <- names ]

    viewDecs = [ viewDec, fromViewDec ]

    viewDec    = funD 'view [viewClause]
    viewClause = clause [ conP 'Q [varP a] ]
                        ( normalB $ TH.tupE [ if pos == l then [| Q $(f (varE a)) |] else [| Q $(first (f (varE a))) |]
                                            | pos <- [1..l]
                                            , let f = foldr (.) id (replicate (pos - 1) second)
                                            ])
                        []

    fromViewDec = funD 'fromView [fromViewClause]
    fromViewClause = clause [ fromViewClausePattern ]
                            ( normalB [| Q  $(fst $ fromViewClauseBody (map varE names)) |] )
                            []

    fromViewClausePattern = tupP (map (\n -> conP 'Q [varP n]) names)

    fromViewClauseBody [a1,b1] =
      let t1 = [| TupleT (typeExp $a1) (typeExp $b1) |]
          e1 = [| TupleE ($a1) ($b1) ($t1) |]
      in  (e1,t1)
    fromViewClauseBody (a1 : as1) =
      let (e1,t1) = fromViewClauseBody as1
          t2 = [| TupleT (typeExp $a1) ($t1) |]
          e2 = [| TupleE ($a1) ($e1) ($t2) |]
      in  (e2,t2)
    fromViewClauseBody _ = $impossible


-- | Generate all 'View' instances for tuples within range.
generateDeriveTupleViewRange :: Int -> Int -> TH.Q [Dec]
generateDeriveTupleViewRange from to =
    concat `fmap` sequenceQ [ deriveTupleView n | n <- reverse [from..to] ]


--------------------------------------------------------------------------------
-- * Deriving Instances for Records
--

-- | Derive the 'QA' instance for a record definition.
deriveQAForRecord :: TH.Q [Dec] -> TH.Q [Dec]
deriveQAForRecord q = (++) <$> q
                           <*> deriveQAForRecord' q

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
             reifyClause = clause [ wildP ]
                                  ( normalB $ applyChainTupleE 'TupleT [ [| reify (undefined :: $(return _t)) |] | (_,_,_t) <- rVar] )
                                  []

             names = [ mkName $ "a" ++ show i | i <- [1..length rVar] ]

             fromNormDec    = funD 'fromNorm [fromNormClause, failClause]
             fromNormClause = clause [ applyChainTupleP (map varP names) ]
                                     ( normalB $ (conE dName) `applyChainE` [ [| fromNorm $(varE n) |]
                                                                            | n <- names
                                                                            ]
                                     )
                                     []

             -- Fail with a verbose message where this happened
             failClause = clause [ wildP ]
                                 ( do loc <- location
                                      let pos = show (TH.loc_filename loc, fst (TH.loc_start loc), snd (TH.loc_start loc))
                                      normalB [| error $ "ferry: Impossible `fromNorm' at location " ++ pos |]
                                 )
                                 []

             toNormDec    = funD 'toNorm [toNormClause]
             toNormClause = clause [ conP dName (map varP names) ]
                                   ( normalB $ fst $ toNormClauseBody $ [ varE n | n <- names ] )
                                   []
                                   
             toNormClauseBody [a1,b1] =
                let t1 = [| TupleT (reify $a1) (reify $b1) |]
                    e1 = [| TupleN (toNorm $a1) (toNorm $b1) ($t1) |]
                in  (e1,t1)
             toNormClauseBody (a1 : as1) =
                let (e1,t1) = toNormClauseBody as1
                    t2 = [| TupleT (reify $a1) ($t1) |]
                    e2 = [| TupleN (toNorm $a1) ($e1) ($t2) |]
                in  (e2,t2)
             toNormClauseBody _ = $impossible


         instanceD rCxt
                   rType
                   rDec

    addInst _ = error "ferry: Failed to derive 'QA' - Invalid record definition"

-- | Derive the 'View' instance for a record definition. See
-- 'deriveQAForRecord' for an example.
deriveViewForRecord :: TH.Q [Dec] -> TH.Q [Dec]
deriveViewForRecord q = (++) <$> q
                             <*> deriveViewForRecord' q

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
            vRec   = recC vName [ return (prefixV n, s, makeQ t) | (n,s,t) <- rVar ]

            prefixV :: Name -> Name
            prefixV n = mkName $ nameBase n ++ "V"

            makeQ :: TH.Type -> TH.Type
            makeQ t = ConT ''Q `AppT` t

            vNames = [] --dNames

        v <- dataD (return [])
                   vName
                   []
                   [vRec]
                   vNames

        -- The instance definition

        let rCxt  = return []
            rType = conT ''View `appT` (conT ''Q `appT` conT dName)
                                `appT` (conT vName)
            rDec  = [ viewDec
                    , fromViewDec
                    ]

            a = mkName "a"

            first  p = [| AppE1 Fst $p (typeTupleFst (typeExp $p)) |]
            second p = [| AppE1 Snd $p (typeTupleSnd (typeExp $p)) |]

            viewDec    = funD 'view [viewClause]
            viewClause = clause [ conP 'Q [varP a] ]
                                ( normalB $ applyChainE (conE vName)
                                          $ map (appE (conE 'Q))
                                          $ [ if pos == length rVar then (f (varE a)) else (first (f (varE a)))
                                            | pos <- [1 .. length rVar]
                                            , let f = foldr (.) id (replicate (pos - 1) second)
                                            ] )
                                []

            -- names for variables used in the `fromView' function
            qs = [ mkName $ "q" ++ show i | i <- [1.. length rVar] ]

            fromViewDec    = funD 'fromView [fromViewClause] --, failClause]
            fromViewClause = clause [ conP vName [ conP 'Q [varP q1] | q1 <- qs ] ]
                                    ( normalB [| Q  $(fst $ fromViewClauseBody (map varE qs)) |] )
                                    []

            fromViewClauseBody [a1,b1] =
              let t1 = [| TupleT (typeExp $a1) (typeExp $b1) |]
                  e1 = [| TupleE ($a1) ($b1) ($t1) |]
              in  (e1,t1)
            fromViewClauseBody (a1 : as1) =
              let (e1,t1) = fromViewClauseBody as1
                  t2 = [| TupleT (typeExp $a1) ($t1) |]
                  e2 = [| TupleE ($a1) ($e1) ($t2) |]
              in  (e2,t2)
            fromViewClauseBody _ = $impossible



            -- Fail with a verbose message where this happened
            failClause = clause [ wildP ]
                                ( do loc <- location
                                     let pos = show (TH.loc_filename loc, fst (TH.loc_start loc), snd (TH.loc_start loc))
                                     normalB [| error $ "ferry: Impossible `fromView' at location " ++ pos |]
                                )
                                []

        i <- instanceD rCxt
                       rType
                       rDec

        return [v,i]

    addView _ = error "ferry: Failed to derive 'View' - Invalid record definition"


-- | Derive 'TA' instances
deriveTAForRecord :: TH.Q [Dec] -> TH.Q [Dec]
deriveTAForRecord q = (++) <$> q
                           <*> deriveTAForRecord' q

deriveTAForRecord' :: TH.Q [Dec] -> TH.Q [Dec]
deriveTAForRecord' q = q >>= mapM addTA
  where
    addTA (DataD [] dName [] [RecC rName (_:_)] _) | dName == rName =

        let taCxt  = return []
            taType = conT ''TA `appT` conT dName
            taDec  = [ ]

        in instanceD taCxt
                     taType
                     taDec

    addTA _ = error "ferry: Failed to derive 'TA' - Invalid record definition"


-- | Create lifted record selectors
recordQSelectors :: TH.Q [Dec] -> TH.Q [Dec]
recordQSelectors q = (++) <$> q
                          <*> recordQSelectors' q

recordQSelectors' :: TH.Q [Dec] -> TH.Q [Dec]
recordQSelectors' q = q >>= fmap join . mapM addSel
  where
    addSel :: Dec -> TH.Q [Dec]
    addSel (DataD [] dName [] [RecC rName vst] _) | dName == rName && not (null vst) =

        let namesAndTypes = [ (n, t')
                            | (n, _, t) <- vst
                            , let t' = arrowChainT [ conT ''Q `appT` conT dName
                                                   , conT ''Q `appT` return t
                                                   ]
                            ]

            addFunD (n,t) = let qn = mkName $ nameBase n ++ "Q"
                                vn = mkName $ nameBase n ++ "V"
                             in sequenceQ [ sigD qn t
                                          , funD qn [ clause []
                                                             (normalB [| $(varE vn) . view |])
                                                             []
                                                    ]
                                          ]

         in if null namesAndTypes
               then error "woot?"
               else concat `fmap` mapM addFunD namesAndTypes

    addSel _ = error "ferry: Failed to create record selectors - Invalid record definition"


--------------------------------------------------------------------------------
-- * Exported enduser functions
--

-- | Lookup a table and create its data type representation
--
-- Example usage:
--
-- > $(createTableRepresentation myConnection "t_user" "User" [''Show, ''Eq])
--
-- Note that this representation is created on compile time, not on run time!
createTableRepresentation :: (IConnection conn)
                          => (IO conn)  -- ^ Database connection
                          -> String     -- ^ Table name
                          -> String     -- ^ Data type name for each row of the table
                          -> [Name]     -- ^ Default deriving instances
                          -> TH.Q [Dec]
createTableRepresentation conn t dname dnames = do
    tdesc <- runIO $ do
        c <- conn
        describeTable c t
    createTableRepresentation' $ createDataType (sortWith fst tdesc)

  where
    createDataType :: [(String, SqlColDesc)] -> TH.Q [Dec]
    createDataType [] = error "ferry: Empty table description"
    createDataType ds = pure `fmap` dataD dCxt
                                          dName
                                          []
                                          [dCon ds]
                                          dNames

    dName     = mkName dname
    dNames    = dnames

    dCxt      = return []
    dCon desc = recC dName (map toVarStrictType desc)

    -- no support for nullable columns yet:
    toVarStrictType (n,SqlColDesc { colType = ty, colNullable = _ }) =
        let t' = case convert ty of
                      IntegerT    -> ConT ''Integer
                      BoolT       -> ConT ''Bool
                      CharT       -> ConT ''Char
                      DoubleT     -> ConT ''Double
                      TextT       -> ConT ''Text
                      TimeT       -> ConT ''UTCTime
                      _           -> $impossible

        in return (mkName n, NotStrict, t')


-- | Derive all necessary instances for record definitions to represent table
-- values.
--
-- Example usage:
--
-- > $(createTableRepresentation' [d|
-- >
-- >     data User = User
-- >         { user_id    :: Int
-- >         , user_name  :: String
-- >         }
-- >
-- >   |])
--
-- This creates the following record type, which can be used with the
-- \"ViewPatterns\" pragma:
--
-- > data V'User = V'User
-- >     { v'user_id    :: Q Int
-- >     , v'user_name  :: Q String
-- >     }
-- >  -- deriving View (Q User) V'User
--
-- And the lifted record selectors:
--
-- > q'user_id      :: Q User -> Q Int
-- > q'user_name    :: Q User -> Q String
createTableRepresentation' :: TH.Q [Dec] -> TH.Q [Dec]
createTableRepresentation' q = do
    d  <- q
    qa <- deriveQAForRecord' q
    v  <- deriveViewForRecord' q
    ta <- deriveTAForRecord' q
    rs <- recordQSelectors' q
    return $ d ++ qa ++ v ++ ta ++ rs
