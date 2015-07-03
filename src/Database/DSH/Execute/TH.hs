{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Execute.TH
    ( mkExecTuple
    , mkTabTupleType
    , mkSegTupleType
    ) where

import           Language.Haskell.TH
import           Data.List

import           Text.Printf

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.TH
import           Database.DSH.Frontend.TupleTypes
import qualified Database.DSH.Frontend.Internals as DSH

--------------------------------------------------------------------------------
-- Common name definitions

tabTupleConsName :: Int -> Name
tabTupleConsName width = mkName $ printf "TTuple%d" width

segTupleConsName :: Int -> Name
segTupleConsName width = mkName $ printf "STuple%d" width

--------------------------------------------------------------------------------
-- Generate the function that executes queries in a tuple layout

elemTyName :: Int -> Q Name
elemTyName i = newName $ printf "ty%d" i

elemLytName :: Int -> Q (Name, Name)
elemLytName i = (,) <$> newName (printf "lyt%d" i)
                    <*> newName (printf "lyt%d'" i)


-- | Generate the recursive call to 'execNested'
-- 'lyt<n>' <- execNested conn lyt<n> ty<n>'
mkExecNestedStmt :: Name -> Name -> Name -> Stmt
mkExecNestedStmt tyName lytName resLytName =
    let execNested = VarE $ mkName "execNested"
        conn       = VarE $ mkName "conn"
        callE      = AppE (AppE (AppE execNested conn) (VarE lytName)) (VarE tyName)

    in BindS (VarP resLytName) callE

-- | Generate the case for one particular tuple type
mkExecTupleMatch :: Int -> Q Match
mkExecTupleMatch width = do
    tyNames               <- mapM elemTyName [1..width]
    (lytNames, lytNames') <- unzip <$> mapM elemLytName [1..width]

    -- '([lyt1, ..., lyt<n>], Tuple<n>T ty1 ... ty<n>)'
    let pat = TupP [ ListP $ map VarP lytNames
                   , ConP (tupTyConstName "F" width) (map VarP tyNames)
                   ]

    -- 'return $ STuple $ STuple<n> ty lyt1 ... lyt<n>'
    let execNestedStmts = zipWith3 mkExecNestedStmt tyNames lytNames lytNames'
        returnStmt      = NoBindS $ AppE (VarE 'return)
                                  $ AppE (ConE $ mkName "STuple")
                                  $ foldl' AppE
                                           (AppE (ConE $ segTupleConsName width) (VarE $ mkName "ty"))
                                           (map VarE lytNames')


    return $ Match pat (NormalB $ DoE $ execNestedStmts ++ [returnStmt]) []

-- | Generate a lambda expression that matches on a tuple type layout
-- and recursively calls execNested on the tuple member layouts.
-- @
-- \lyts ty ->
--  case (lyts, ty) of
--      ([lyt1, ..., lyt<n>], Tuple<n>T ty1 ... ty<n>) -> do
--          lyt1' <- execNested conn lyt1 ty1
--          ...
--          lyt<n>' <- execNested conn lyt<n> ty<n>
--          return $ STuple $ STuple<n> ty lyt1 ... lyt<n>
-- @
--
-- The lambda expression is /not/ closed: The names 'conn' and 'ty' must be in
-- scope where 'conn' is the database connection and 'ty' is the tuple type being
-- dissected.
mkExecTuple :: Int -> Q Exp
mkExecTuple maxWidth = do
    lytName       <- newName "lyts"
    tyName        <- newName "tys"

    tupMatches    <- mapM mkExecTupleMatch [2..maxWidth]
    impossibleExp <- impossible
    let matches = tupMatches ++ [Match WildP (NormalB impossibleExp) []]

    let lamBody = CaseE (TupE [VarE lytName, VarE tyName]) matches
    return $ LamE [VarP lytName, VarP tyName] lamBody

--------------------------------------------------------------------------------
-- Generate tuple layout type containing individual query results or
-- segmaps. The code generated for both is mostly identical except for
-- the layout type constructor and the constructor names.

tupElemTyName :: Int -> Q Name
tupElemTyName i = newName $ printf "t%d" i

-- | Generate a single constructor for the 'TabTuple' type.
mkTupleLytCons :: Name -> (Type -> Type) -> (Int -> Name) -> Int -> Q Con
mkTupleLytCons tupTyName lytTyCons conName width = do

    tupElemTyNames <- mapM tupElemTyName [1..width]

    let tyVarBinders     = map PlainTV tupElemTyNames

        -- (t1, ..., t<n>)
        tupTy            = foldl' AppT (TupleT width)
                           $ map VarT tupElemTyNames

        -- a ~ (t1, ..., t<n>)
        tupConstraint    = equalConstrTy (VarT tupTyName) tupTy

        -- Reify t1, ..., Reify t<n>
        reifyConstraints = map (\n -> nameTyApp ''DSH.Reify (VarT n)) tupElemTyNames

        constraints      = tupConstraint : reifyConstraints

    let -- 'Type a'
        dshTypeTy  = (NotStrict, AppT (ConT ''DSH.Type) (VarT tupTyName))
        -- 'TabLayout t1, TabLayout t<n>
        elemLytTys = [ (NotStrict, lytTyCons (VarT t)) -- AppT (ConT $ mkName "TabLayout") (VarT t))
                     | t <- tupElemTyNames
                     ]
        argTys     = dshTypeTy : elemLytTys

    return $ ForallC tyVarBinders constraints
           $ NormalC (conName width) {- (tabTupleConsName width) -} argTys

-- | Generate the data type for 'TabTuple'/'SegTuple' layouts that contain
-- tabular query results.
-- @
-- data TabTuple a where
--     TTuple3 :: (Reify t1, ..., Reify t<n>) => Type (t1, ..., t<n>)
--                                            -> TabLayout t1
--                                            -> ...
--                                            -> TabLayout t<n>
--                                            -> TabTuple (t1, ..., t<n>)
-- @
--
-- Because TH does not directly support GADT syntax, we have to
-- emulate it using explicit universal quantification:
--
-- @
-- data TabTuple a =
--     forall t1, ..., t<n>. a ~ (t1, ..., t<n>),
--                           Reify t1,
--                           ...
--                           Reify t<n> =>
--                           Type a -> TabLayout t1 -> ... -> TabLayout t<n>
-- @
mkTupleLyt :: Name -> (Type -> Type) -> (Int -> Name) -> Int -> Q [Dec]
mkTupleLyt tyName lytTyCons conName maxWidth = do
    tupTyName <- newName "a"
    cons      <- mapM (mkTupleLytCons tupTyName lytTyCons conName) [2..maxWidth]

    return $ [DataD [] tyName  [PlainTV tupTyName] cons []]

--------------------------------------------------------------------------------
-- Generate the tuple layout type containing tabular results

mkTabTupleType :: Int -> Q [Dec]
mkTabTupleType maxWidth = mkTupleLyt tabTupleTyName tabLayoutTyCons tabTupleConsName maxWidth
  where
    tabLayoutTyCons :: Type -> Type
    tabLayoutTyCons argTy = AppT (ConT $ mkName "TabLayout") argTy

    tabTupleTyName :: Name
    tabTupleTyName = mkName "TabTuple"

--------------------------------------------------------------------------------
-- Generate the tuple layout type containing segment maps

mkSegTupleType :: Int -> Q [Dec]
mkSegTupleType maxWidth = mkTupleLyt segTupleTyName segLayoutTyCons segTupleConsName maxWidth
  where
    segLayoutTyCons :: Type -> Type
    segLayoutTyCons argTy = AppT (ConT $ mkName "SegLayout") argTy

    segTupleTyName :: Name
    segTupleTyName = mkName "SegTuple"
