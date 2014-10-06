{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Frontend.TupleTypes
    ( mkQAInstances
    , mkTAInstances
    , mkTupleConstructors
    , mkTupElemType
    , mkTupElemCompile
    , mkReifyInstances
    , mkTranslateTupleTerm
    ) where

import           Control.Applicative
import           Data.List
import           Text.Printf

import           Language.Haskell.TH

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

tupAccName :: Int -> Int -> Name
tupAccName width elemIdx = mkName $ printf "Tup%d_%d" width elemIdx
    
mkTupElemCon :: Name -> Name -> [Name] -> Int -> Int -> Q Con
mkTupElemCon aTyVar bTyVar boundTyVars width elemIdx = do
    let binders   = map PlainTV boundTyVars
    let tupleType = mkTupType elemIdx width boundTyVars bTyVar
    let con       = tupAccName width elemIdx
    let ctx       = [EqualP (VarT aTyVar) tupleType]
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

    return $ [DataD [] tyName tyVars cons []]
 
--------------------------------------------------------------------------------
-- Translation of tuple accessors to CL

mkCompileMatch :: Name -> (Name, Int) -> Q Match
mkCompileMatch exprName (con, elemIdx) = do
    let translateVar = return $ VarE $ mkName "translate"
        exprVar      = return $ VarE exprName
        idxLit       = return $ LitE $ IntegerL $ fromIntegral elemIdx
    bodyExp  <- [| CP.tupElem (intIndex $idxLit) <$> $translateVar $exprVar |]
    let body = NormalB $ bodyExp
    return $ Match (ConP con []) body []

mkTupElemCompile :: Int -> Q Exp
mkTupElemCompile maxWidth = do
    let cons = concat [ [ (tupAccName width idx, idx)
                        | idx <- [1..width] 
                        ] 
                      | width <- [2..maxWidth] 
                      ]

    exprName <- newName "e"
    opName   <- newName "te"

    matches  <- mapM (mkCompileMatch exprName) cons

    let lamBody = CaseE (VarE opName) matches
    return $ LamE [VarP opName, VarP exprName] lamBody

--------------------------------------------------------------------------------
-- Reify instances for tuple types

reifyType :: Name -> Exp
reifyType tyName = AppE (VarE $ mkName "reify") (SigE (VarE 'undefined) (VarT tyName))

mkReifyFun :: [Name] -> Dec
mkReifyFun tyNames =
    let argTys         = map reifyType tyNames
        tupTyConstName = mkName $ printf "Tuple%dT" (length tyNames)
        body           = AppE (ConE $ mkName "TupleT") (foldl' AppE (ConE tupTyConstName) argTys)
    in FunD (mkName "reify") [Clause [WildP] (NormalB body) []]

mkReifyInstance :: Int -> Dec
mkReifyInstance width =
    let tyNames  = map (\i -> mkName $ "t" ++ show i) [1..width]
        tupTy    = foldl' AppT (TupleT width) $ map VarT tyNames
        instTy   = AppT (ConT $ mkName "Reify") tupTy
        reifyCxt = map (\tyName -> ClassP (mkName "Reify") [VarT tyName]) tyNames
        
    in InstanceD reifyCxt instTy [mkReifyFun tyNames]

mkReifyInstances :: Int -> Q [Dec]
mkReifyInstances maxWidth = return $ map mkReifyInstance [2..maxWidth]

--------------------------------------------------------------------------------
-- QA instances for tuple types

outerConst :: Name
outerConst = mkName "TupleConstE"

innerConst :: Int -> Name
innerConst width = mkName $ printf "Tuple%dE" width

mkToExp :: Int -> [Name] -> Dec
mkToExp width elemNames =
    let toExpVar   = VarE $ mkName "toExp"
        elemArgs   = map (\n -> AppE toExpVar (VarE n)) elemNames
        body       = NormalB $ AppE (ConE outerConst) 
                             $ foldl' AppE (ConE $ innerConst width) elemArgs
        tupClause  = Clause [TupP $ map VarP elemNames] body []
    in FunD (mkName "toExp") [tupClause]

mkFrExp :: Int -> [Name] -> Q Dec
mkFrExp width elemNames = do
    impossibleExpr <- [| error $(litE $ StringL $ printf "frExp %d" width) |]
    let tupPattern       = ConP outerConst [ConP (innerConst width) (map VarP elemNames) ]
        tupleExpr        = TupE $ map (\n -> AppE (VarE $ mkName "frExp") (VarE n)) elemNames
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
        tupTy   = foldl' AppT (TupleT width) $ map VarT tyNames
        instTy  = AppT (ConT $ mkName "QA") tupTy
        qaCxt   = map (\tyName -> ClassP (mkName "QA") [VarT tyName]) tyNames
        rep     = mkRep width tyNames tupTy
        toExp   = mkToExp width tyNames
    frExp <- mkFrExp width tyNames
    return $ InstanceD qaCxt instTy [rep, toExp, frExp]

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
        taCxt   = map (\tyName -> ClassP (mkName "BasicType") [VarT tyName]) tyNames
    in InstanceD taCxt instTy []

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

qName :: Name
qName = mkName "Q"

mkArrowTy :: Type -> Type -> Type
mkArrowTy domTy coDomTy = AppT (AppT ArrowT domTy) coDomTy

mkTupleConstructor :: Int -> [Dec]
mkTupleConstructor width =
    let tyNames   = map (\i -> mkName $ "t" ++ show i) [1..width]

        -- Type stuff
        tupTy     = AppT (ConT qName) $ foldl' AppT (TupleT width) $ map VarT tyNames
        elemTys   = map (AppT (ConT qName)) $ map VarT tyNames
        arrowTy   = foldr mkArrowTy tupTy elemTys
        qaConstr  = map (\n -> ClassP (mkName "QA") [VarT n]) tyNames
        funTy     = ForallT (map PlainTV tyNames) qaConstr arrowTy

        -- Term stuff
        qPats     = map (\n -> ConP qName [VarP n]) tyNames 
        tupConApp = foldl' AppE (ConE $ innerConst width) $ map VarE tyNames
        bodyExp   = AppE (ConE qName) (AppE (ConE outerConst) tupConApp)

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
        matchPat  = ConP (innerConst width) (map VarP subTermNames)
    return $ Match matchPat (NormalB matchBody) []

-- | Generate the lambda expression that translates frontend tuple
-- value constructors into CL tuple constructors.
mkTranslateTupleTerm :: Int -> Q Exp
mkTranslateTupleTerm maxWidth = do
    lamArgName <- newName "tupleConst"

    matches  <- mapM mkTranslateTermMatch [2..maxWidth]

    let lamBody = CaseE (VarE lamArgName) matches
    return $ LamE [VarP lamArgName] lamBody
