{-# LANGUAGE TemplateHaskell #-}


-- | Generate AST types, functions and instances for tuples.
module Database.DSH.Frontend.TupleTypes
    ( -- * Generate tuple types, functions and instances
      mkQAInstances
    , mkTAInstances
    , mkTupleConstructors
    , mkTupleAccessors
    , mkTupElemType
    , mkTupElemCompile
    , mkReifyInstances
    , mkTranslateTupleTerm
    , mkTranslateType
    , mkViewInstances
    , mkTupleAstComponents
    -- * Helper functions
    , innerConst
    , outerConst
    , tupAccName
    , mkTupElemTerm
    , mkTupConstTerm
    , tupTyConstName
    ) where

import           Data.List
import           Text.Printf

import           Language.Haskell.TH

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.TH
import           Database.DSH.Common.Nat
import qualified Database.DSH.Common.Type   as T
import qualified Database.DSH.CL.Primitives as CP
import qualified Database.DSH.CL.Lang       as CL

--------------------------------------------------------------------------------
-- Tuple Accessors

-- | Generate all constructors for a given tuple width.
mkTupElemCons :: Name -> Name -> Int -> Q [Con]
mkTupElemCons aTyVar bTyVar width = do
    boundTyVars <- mapM (\i -> newName $ printf "t%d" i) [1..width-1]
    mapM (mkTupElemCon aTyVar bTyVar boundTyVars width) [1..width]

mkTupType :: Int -> Int -> [Name] -> Name -> Type
mkTupType elemIdx width boundTyVars bTyVar =
    let elemTys = map VarT $ take (elemIdx - 1) boundTyVars
                             ++ [bTyVar]
                             ++ drop (elemIdx - 1) boundTyVars
    in foldl' AppT (TupleT width) elemTys

mkTupElemCon :: Name -> Name -> [Name] -> Int -> Int -> Q Con
mkTupElemCon aTyVar bTyVar boundTyVars width elemIdx = do
    let binders = map PlainTV boundTyVars
    let tupTy   = mkTupType elemIdx width boundTyVars bTyVar
    let con     = tupAccName width elemIdx
    let ctx     = [equalConstrTy (VarT aTyVar) tupTy]
    return $ ForallC binders ctx (NormalC con [])

-- | Generate the complete type of tuple acccessors for all tuple
-- widths.
--
-- @
-- data TupElem a b where
--     Tup2_1 :: TupElem (a, b) a
--     Tup2_2 :: TupElem (a, b) b
--     Tup3_1 :: TupElem (a, b, c) a
--     Tup3_2 :: TupElem (a, b, c) b
--     Tup3_3 :: TupElem (a, b, c) c
--     ...
-- @
--
-- Due to the lack of support for proper GADT syntax in TH, we have
-- to work with explicit universal quantification:
--
-- @
-- data TupElem a b =
--     | forall d. a ~ (b, d) => Tup2_1
--     | forall d. a ~ (d, b) => Tup2_2
--
--     | forall d e. a ~ (b, d, e) => Tup3_1
--     | forall d e. a ~ (d, b, e) => Tup3_2
--     | forall d e. a ~ (d, e, b) => Tup3_3
--     ...
-- @
mkTupElemType :: Int -> Q [Dec]
mkTupElemType maxWidth = do
    let tyName = mkName "TupElem"

    aTyVar <- newName "a"
    bTyVar <- newName "b"
    let tyVars = map PlainTV [aTyVar, bTyVar]

    cons   <- concat <$> mapM (mkTupElemCons aTyVar bTyVar) [2..maxWidth]

    return $ [DataD [] tyName tyVars Nothing cons []]

--------------------------------------------------------------------------------
-- Translation of tuple accessors to CL

-- TupElem a b -> Exp a -> Compile CL.Expr
-- \te e ->
--     case te of
--         Tup{2}_{1} -> CP.tupElem (indIndex 1) <$> translate e
--         Tup{2}_{k} -> CP.tupElem (indIndex k) <$> translate e
--         Tup{3}_{1} -> CP.tupElem (indIndex 1) <$> translate e
--         ...
--         Tup{n}_{j} -> CP.tupElem (indIndex j) <$> translate e

-- FIXME mkTupElemCompile does not depend on 'translate'
-- anymore. Therefore, we could inject a regular global binding for
-- the function instead of a lambda.

mkCompileMatch :: (Name, Int) -> Q Match
mkCompileMatch (con, elemIdx) = do
    let idxLit       = return $ LitE $ IntegerL $ fromIntegral elemIdx
    bodyExp  <- [| CP.tupElem (intIndex $idxLit)  |]
    let body = NormalB $ bodyExp
    return $ Match (ConP con []) body []

mkTupElemCompile :: Int -> Q Exp
mkTupElemCompile maxWidth = do
    let cons = concat [ [ (tupAccName width idx, idx)
                        | idx <- [1..width]
                        ]
                      | width <- [2..maxWidth]
                      ]

    opName   <- newName "te"
    matches  <- mapM mkCompileMatch cons

    let lamBody = CaseE (VarE opName) matches
    return $ LamE [VarP opName] lamBody

--------------------------------------------------------------------------------
-- Reify instances for tuple types

reifyType :: Name -> Exp
reifyType tyName = AppE (VarE $ mkName "reify") (SigE (VarE 'undefined) (VarT tyName))

mkReifyFun :: [Name] -> Dec
mkReifyFun tyNames =
    let argTys         = map reifyType tyNames
        body           = AppE (ConE $ mkName "TupleT")
                         $ foldl' AppE (ConE $ tupTyConstName "" $ length tyNames) argTys
    in FunD (mkName "reify") [Clause [WildP] (NormalB body) []]

mkReifyInstance :: Int -> Dec
mkReifyInstance width =
    let tyNames  = map (\i -> mkName $ "t" ++ show i) [1..width]
        instTy   = AppT (ConT $ mkName "Reify") $ tupleType $ map VarT tyNames
        reifyCxt = map (\tyName -> nameTyApp (mkName "Reify") (VarT tyName)) tyNames

    in InstanceD Nothing reifyCxt instTy [mkReifyFun tyNames]

mkReifyInstances :: Int -> Q [Dec]
mkReifyInstances maxWidth = return $ map mkReifyInstance [2..maxWidth]

--------------------------------------------------------------------------------
-- QA instances for tuple types

mkToExp :: Int -> [Name] -> Dec
mkToExp width elemNames =
    let toExpVar   = VarE $ mkName "toExp"
        elemArgs   = map (\n -> AppE toExpVar (VarE n)) elemNames
        body       = NormalB $ AppE (ConE $ outerConst "")
                             $ foldl' AppE (ConE $ innerConst "" width) elemArgs
        tupClause  = Clause [TupP $ map VarP elemNames] body []
    in FunD (mkName "toExp") [tupClause]

mkFrExp :: Int -> [Name] -> Q Dec
mkFrExp width elemNames = do
    impossibleExpr <- [| error $(litE $ StringL $ printf "frExp %d" width) |]
    let tupPattern       = ConP (outerConst "")
                                [ConP (innerConst "" width) (map VarP elemNames) ]
        tupleExpr        = TupE $ map (\n -> AppE (VarE $ mkName "frExp") (VarE n))
                                      elemNames
        tupleClause      = Clause [tupPattern] (NormalB tupleExpr) []
        impossibleClause = Clause [WildP] (NormalB impossibleExpr) []
    return $ FunD (mkName "frExp") [tupleClause, impossibleClause]

mkRep :: Int -> [Name] -> Type -> Dec
mkRep width tyNames tupTyPat =
    let resTy    = foldl' AppT (TupleT width)
                   $ map (AppT $ ConT $ mkName "Rep")
                   $ map VarT tyNames
    in TySynInstD (mkName "Rep") (TySynEqn [tupTyPat] resTy)

mkQAInstance :: Int -> Q Dec
mkQAInstance width = do
    let tyNames = map (\i -> mkName $ "t" ++ show i) [1..width]
        tupTy   = tupleType $ map VarT tyNames
        instTy  = AppT (ConT $ mkName "QA") tupTy
        qaCxt   = map (\tyName -> nameTyApp (mkName "QA") (VarT tyName)) tyNames
        rep     = mkRep width tyNames tupTy
        toExp   = mkToExp width tyNames
    frExp <- mkFrExp width tyNames
    return $ InstanceD Nothing qaCxt instTy [rep, toExp, frExp]

-- | Generate QA instances for tuple types according to the following template:
--
-- @
-- instance (QA t1, ..., QA tn) => QA (t1, ..., tn) where
--   type Rep (t1, ..., tn) = (Rep t1, ..., Rep tn)
--   toExp (v1, ..., vn) = TupleConstE (Tuple<n>E (toExp v1) ... (toExp vn))
--   frExp (TupleConstE (Tuple<n>E v1 ... vn)) = (frExp v1, ... b, frExp vn)
--   frExp _ = $impossible
-- @
mkQAInstances :: Int -> Q [Dec]
mkQAInstances maxWidth = mapM mkQAInstance [2..maxWidth]

--------------------------------------------------------------------------------
-- TA instances for tuple types

mkTAInstance :: Int -> Dec
mkTAInstance width =
    let tyNames = map (\i -> mkName $ "t" ++ show i) [1..width]
        tupTy   = foldl' AppT (TupleT width) $ map VarT tyNames
        instTy  = AppT (ConT $ mkName "TA") tupTy
        taCxt   = map (\tyName -> nameTyApp (mkName "BasicType") (VarT tyName)) tyNames
    in InstanceD Nothing taCxt instTy []

-- | Generate TA instances for tuple types according to the following template:
--
-- @
-- instance (BasicType t1, ..., BasicType tn) => TA (t1, ..., tn) where
-- @
mkTAInstances :: Int -> Q [Dec]
mkTAInstances maxWidth = return $ map mkTAInstance [2..maxWidth]

--------------------------------------------------------------------------------
-- Smart constructors for tuple values

tupConName :: Int -> Name
tupConName width = mkName $ printf "tup%d" width

mkArrowTy :: Type -> Type -> Type
mkArrowTy domTy coDomTy = AppT (AppT ArrowT domTy) coDomTy

mkTupleConstructor :: Int -> [Dec]
mkTupleConstructor width =
    let tyNames   = map (\i -> mkName $ "t" ++ show i) [1..width]

        -- Type stuff
        tupTy     = AppT (ConT qName) $ foldl' AppT (TupleT width) $ map VarT tyNames
        elemTys   = map (AppT (ConT qName)) $ map VarT tyNames
        arrowTy   = foldr mkArrowTy tupTy elemTys
        qaConstr  = map (\n -> nameTyApp (mkName "QA") (VarT n)) tyNames
        funTy     = ForallT (map PlainTV tyNames) qaConstr arrowTy

        -- Term stuff
        qPats     = map (\n -> ConP qName [VarP n]) tyNames
        tupConApp = foldl' AppE (ConE $ innerConst "" width) $ map VarE tyNames
        bodyExp   = AppE (ConE qName) (AppE (ConE $ outerConst "") tupConApp)

        sig       = SigD (tupConName width) funTy
        body      = FunD (tupConName width) [Clause qPats (NormalB bodyExp) []]
    in [sig, body]

-- | Construct smart constructors for tuple types according to the
-- following template.
--
-- @
-- tup<n> :: (QA t1, ...,QA tn) => Q t1 -> ... -> Q tn -> Q (t1, ..., tn)
-- tup<n> (Q v1) ... (Q vn)= Q (TupleConstE (Tuple<n>E v1 ... vn))
-- @
mkTupleConstructors :: Int -> Q [Dec]
mkTupleConstructors maxWidth = return $ concatMap mkTupleConstructor [2..maxWidth]

--------------------------------------------------------------------------------
-- Tuple accessors

mkTupleAccessor :: Int -> Int -> Q [Dec]
mkTupleAccessor width idx = do
    -- Construct the function type
    fieldTyName       <- newName "a"
    otherFieldTyNames <- mapM (\i -> newName $ printf "b%d" i) [1..width-1]
    let elemTyNames = take (idx - 1) otherFieldTyNames
                      ++ [fieldTyName]
                      ++ drop (idx - 1) otherFieldTyNames
        elemTyVars = map VarT elemTyNames
        qaCxt   = map (\tyName -> nameTyApp (mkName "QA") (VarT tyName)) elemTyNames
        tupTy   = AppT (ConT qName) $ foldl' AppT (TupleT width) elemTyVars
        fieldTy = AppT (ConT qName) (VarT fieldTyName)
        arrowTy = mkArrowTy tupTy fieldTy
        funTy   = ForallT (map PlainTV elemTyNames) qaCxt arrowTy
        funSig  = SigD (tupAccFunName width idx) funTy

    -- Construct the function equation
    exprName <- newName "e"
    funBody <- appE (conE qName) $ mkTupElemTerm width idx (VarE exprName)
    let qPat = ConP qName [VarP exprName]
        funDef = FunD (tupAccFunName width idx) [Clause [qPat] (NormalB funBody) []]

    return [funSig, funDef]

-- | Construct field accessor functions for tuple types.
--
-- @
-- tup<n>_<i> :: (QA t1, ..., QA t_n) => Q (t_1, ..., t_n) -> Q t_i
-- tup<n>_<i> (Q e) = Q (AppE (TupElem Tup<n>_<i>) e)
-- @
mkTupleAccessors :: Int -> Q [Dec]
mkTupleAccessors maxWidth = concat <$> sequence [ mkTupleAccessor width idx
                                                | width <- [2..maxWidth]
                                                , idx   <- [1..width]
                                                ]

--------------------------------------------------------------------------------
-- Translation function for tuple constructors in terms

{-
\t -> case t of
    Tuple2E a b -> do
        a' <- translate a
        b' <- translate b
        return $ CL.MkTuple (T.TupleT $ map T.typeOf [a', b']) [a', b']
    Tuple3E a b c -> ...
-}

mkTransBind :: Name -> Name -> Stmt
mkTransBind argName resName =
    BindS (VarP resName) (AppE (VarE $ mkName "translate") (VarE argName))

-- | Generate the translation case for a particular tuple value
-- constructor.
mkTranslateTermMatch :: Int -> Q Match
mkTranslateTermMatch width = do
    let names          = map (\c -> [c]) $ take width ['a' .. 'z']
        subTermNames   = map mkName names
        transTermNames = map (mkName . (++ "'")) names
        transBinds     = zipWith mkTransBind subTermNames transTermNames

        transTerms     = listE $ map varE transTermNames
    conStmt <- NoBindS <$>
               [| return $ CL.MkTuple (T.TupleT $ map T.typeOf $transTerms) $transTerms |]
    let matchBody = DoE $ transBinds ++ [conStmt]
        matchPat  = ConP (innerConst "" width) (map VarP subTermNames)
    return $ Match matchPat (NormalB matchBody) []

-- | Generate the lambda expression that translates frontend tuple
-- value constructors into CL tuple constructors.
mkTranslateTupleTerm :: Int -> Q Exp
mkTranslateTupleTerm maxWidth = do
    lamArgName <- newName "tupleConst"

    matches    <- mapM mkTranslateTermMatch [2..maxWidth]

    let lamBody = CaseE (VarE lamArgName) matches
    return $ LamE [VarP lamArgName] lamBody

--------------------------------------------------------------------------------
-- Translation function for tuple types

{-
\t -> case t of
    Tuple3T t1 t2 t3 -> T.TupleT [translateType t1, translateType t2, translateType t3]
-}

mkTranslateTypeMatch :: Int -> Q Match
mkTranslateTypeMatch width = do
    let subTyNames   = map mkName $ map (\c -> [c]) $ take width ['a' .. 'z']
        matchPat     = ConP (tupTyConstName "" width) (map VarP subTyNames)
        transElemTys = ListE $ map (\n -> AppE (VarE $ mkName "translateType") (VarE n)) subTyNames

    let matchBody  = AppE (ConE 'T.TupleT) transElemTys

    return $ Match matchPat (NormalB matchBody) []

mkTranslateType :: Int -> Q Exp
mkTranslateType maxWidth = do
    lamArgName <- newName "typeConst"
    matches    <- mapM mkTranslateTypeMatch [2..maxWidth]

    let lamBody = CaseE (VarE lamArgName) matches
    return $ LamE [VarP lamArgName] lamBody

--------------------------------------------------------------------------------
-- View instances

{-
instance (QA a,QA b,QA c) => View (Q (a,b,c)) where
    type ToView (Q (a,b,c)) = (Q a,Q b,Q c)
    view (Q e) = ( Q (AppE (TupElem Tup3_1) e)
                 , Q (AppE (TupElem Tup3_2) e)
                 , Q (AppE (TupElem Tup3_3) e)
                 )
-}

mkToView :: [Name] -> Type -> Dec
mkToView names tupTyPat =
    let qTupPat  = AppT (ConT qName) tupTyPat
        resTupTy = tupleType $ map (\n -> AppT (ConT qName) (VarT n)) names
    in TySynInstD (mkName "ToView") (TySynEqn [qTupPat] resTupTy)

mkViewFun :: Int -> Q Dec
mkViewFun width = do
    expName <- newName "e"
    let expVar      = VarE expName
        qPat        = ConP qName [VarP expName]

    viewBodyExp <- TupE <$> mapM (\idx -> appE (conE qName) $ mkTupElemTerm width idx expVar)
                                 [1..width]

    let viewClause  = Clause [qPat] (NormalB viewBodyExp) []

    return $ FunD (mkName "view") [viewClause]

mkViewInstance :: Int -> Q Dec
mkViewInstance width = do
    let names     = map (\i -> mkName $ "t" ++ show i) [1..width]
        tupTy     = tupleType $ map VarT names
        instTy    = AppT (ConT $ mkName "View") (AppT (ConT qName) tupTy)

        viewCxt   = map (\n -> nameTyApp (mkName "QA") (VarT n)) names
        toViewDec = mkToView names tupTy
    viewDec <- mkViewFun width
    return $ InstanceD Nothing viewCxt instTy [toViewDec, viewDec]

mkViewInstances :: Int -> Q [Dec]
mkViewInstances maxWidth = mapM mkViewInstance [2..maxWidth]

--------------------------------------------------------------------------------
-- Generate the 'TupleConst' type

tupElemTyName :: Int -> Q Name
tupElemTyName i = newName $ printf "t%d" i

-- | Generate a single constructor for the 'TabTuple' type.
mkTupleCons :: Name -> (Int -> Name) -> (Type -> Type) -> Int -> Q Con
mkTupleCons tupTyName conName elemTyCons width = do

    tupElemTyNames <- mapM tupElemTyName [1..width]

    let tyVarBinders     = map PlainTV tupElemTyNames

        -- (t1, ..., t<n>)
        tupTy            = foldl' AppT (TupleT width)
                           $ map VarT tupElemTyNames

        -- a ~ (t1, ..., t<n>)
        tupConstraint    = equalConstrTy (VarT tupTyName) tupTy

        -- Reify t1, ..., Reify t<n>
        reifyConstraints = map (\n -> nameTyApp (mkName "Reify") (VarT n)) tupElemTyNames

        constraints      = tupConstraint : reifyConstraints

    let -- '(Exp/Type t1) ... (Exp/Type t<n>)'
        elemTys = [ (strict, elemTyCons (VarT t))
                  | t <- tupElemTyNames
                  ]

    return $ ForallC tyVarBinders constraints
           $ NormalC (conName width) elemTys
  where
    strict = Bang NoSourceUnpackedness SourceStrict
-- | Generate the types for AST type and term tuple constructors: 'TupleConst' and
-- 'TupleType'. The first parameter is the name of the type. The second parameter
-- is the type constructor for element fields and the third parameter generates
-- the constructor name for a given tuple width.
--
-- @
-- data TupleConst a where
--     Tuple<n>E :: (Reify t1, ..., Reify t<n>) => Exp t1
--                                              -> ...
--                                              -> Exp t<n>
--                                              -> TupleConst (t1, ..., t<n>)
-- @
--
-- Because TH does not directly support GADT syntax, we have to
-- emulate it using explicit universal quantification:
--
-- @
-- data TupleConst a =
--     forall t1, ..., t<n>. a ~ (t1, ..., t<n>),
--                           Reify t1,
--                           ...
--                           Reify t<n> =>
--                           Exp t1 -> ... -> Exp t<n>
-- @
mkTupleASTTy :: Name -> (Type -> Type) -> (Int -> Name) -> Int -> Q [Dec]
mkTupleASTTy tyName elemTyCons conName maxWidth = do
    tupTyName <- newName "a"
    cons      <- mapM (mkTupleCons tupTyName conName elemTyCons) [2..maxWidth]

    return [DataD [] tyName [PlainTV tupTyName] Nothing cons []]

-- | Generate the 'TupleConst' AST type for tuple term construction
mkAstTupleConst :: Int -> Q [Dec]
mkAstTupleConst maxWidth =
    mkTupleASTTy (mkName "TupleConst") expCon (innerConst "") maxWidth
  where
    expCon = AppT $ ConT $ mkName "Exp"

-- | Generate the 'TupleConst' AST type for tuple term construction
mkAstTupleType :: Int -> Q [Dec]
mkAstTupleType maxWidth =
    mkTupleASTTy (mkName "TupleType") expCon (tupTyConstName "") maxWidth
  where
    expCon = AppT $ ConT $ mkName "Type"

mkTupleAstComponents :: Int -> Q [Dec]
mkTupleAstComponents maxWidth = (++) <$> mkAstTupleConst maxWidth <*> mkAstTupleType maxWidth



--------------------------------------------------------------------------------
-- Helper functions

-- | The name of the constructor that constructs a tuple construction
-- term.
outerConst :: String -> Name
outerConst "" = mkName "TupleConstE"
outerConst m  = mkName $ printf "%s.TupleConstE" m

-- | The name of the constructor for a given tuple width.
innerConst :: String -> Int -> Name
innerConst "" width = mkName $ printf "Tuple%dE" width
innerConst m  width = mkName $ printf "%s.Tuple%dE" m width

-- | The name of a tuple access constructor for a given tuple width
-- and element index.
tupAccName :: Int -> Int -> Name
tupAccName width elemIdx = mkName $ printf "Tup%d_%d" width elemIdx

-- | The name of a tuple access function for a given tuple width and element
-- index.
tupAccFunName :: Int -> Int -> Name
tupAccFunName width elemIdx = mkName $ printf "tup%d_%d" width elemIdx

-- | The name of the tuple type constructor for a given tuple width.
tupTyConstName :: String -> Int -> Name
tupTyConstName "" width = mkName $ printf "Tuple%dT" width
tupTyConstName m  width = mkName $ printf "%s.Tuple%dT" m width

-- |
tupleType :: [Type] -> Type
tupleType elemTypes = foldl' AppT (TupleT width) elemTypes
  where
    width = length elemTypes

qName :: Name
qName = mkName "Q"

-- | Construct a DSH term that accesses a specificed tuple element.
mkTupElemTerm :: Int -> Int -> Exp -> Q Exp
mkTupElemTerm width idx arg = do
    let ta = ConE $ tupAccName width idx
    return $ AppE (AppE (ConE $ mkName "AppE") (AppE (ConE $ mkName "TupElem") ta)) arg

-- | From a list of operand terms, construct a DSH tuple term.
mkTupConstTerm :: [Exp] -> Q Exp
mkTupConstTerm ts
    | length ts <= 16 = return $ AppE (ConE $ mkName "TupleConstE")
                               $ foldl' AppE (ConE $ innerConst "" $ length ts) ts
    | otherwise       = impossible
