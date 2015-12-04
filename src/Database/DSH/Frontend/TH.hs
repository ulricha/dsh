{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Frontend.TH
    ( deriveDSH
    , deriveQA
    , deriveTA
    , deriveView
    , deriveElim
    , deriveSmartConstructors
    , generateTableSelectors
    -- FIXME don't expose tuple constructors but use qualified names
    , DSH.TupleConst(..)
    , F.TupElem(..)
    , DSH.Exp(..)
    , F.Fun(..)
    ) where

import           Control.Monad
import           Data.Char
import           Data.List
import           Data.Maybe

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

import qualified Database.DSH.Frontend.Internals  as DSH
import           Database.DSH.Frontend.TupleTypes
import qualified Database.DSH.Frontend.Builtins   as F
import           Database.DSH.Common.Impossible
import           Database.DSH.Common.TH


-----------------------------------------
-- Deriving all DSH-relevant instances --
-----------------------------------------

deriveDSH :: Name -> Q [Dec]
deriveDSH n = do
  qaDecs    <- deriveQA n
  -- elimDecs  <- deriveElim n
  cc        <- countConstructors n
  viewDecs  <- if cc == 1
                  then deriveView n
                  else return []
  scDecs    <- deriveSmartConstructors n
  return (qaDecs {- ++ elimDecs -} ++ viewDecs ++ scDecs)

-----------------
-- Deriving QA --
-----------------

-- | Derive QA instances for data types and newtypes.
deriveQA :: Name -> Q [Dec]
deriveQA name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt name1 tyVarBndrs cons _names) ->
      deriveTyConQA name1 tyVarBndrs cons
    TyConI (NewtypeD _cxt name1 tyVarBndrs con  _names) ->
      deriveTyConQA name1 tyVarBndrs [con]
    _ -> fail errMsgExoticType

deriveTyConQA :: Name -> [TyVarBndr] -> [Con] -> Q [Dec]
deriveTyConQA name tyVarBndrs cons = do
  roles <- reifyRoles name
  let context = getContext ''DSH.QA roles tyVarBndrs
  let typ           = foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs)
  let instanceHead  = AppT (ConT ''DSH.QA) typ
  let repDec        = deriveRep typ cons
  toExpDec <- deriveToExp cons
  frExpDec <- deriveFrExp cons
  return [InstanceD context instanceHead [repDec,toExpDec,frExpDec]]

-- Deriving the Rep type function

-- | Derive the representation type 'Rep' for a data type
deriveRep :: Type -> [Con] -> Dec
-- GHC-7.8.2 (template-haskell-2.9.0.0) has a trivial but incompatible
-- modification: two arguments of TySynInstD are now encapsulated in a
-- TySynEqn constructor
#if MIN_VERSION_template_haskell(2,9,0)
deriveRep typ cons = TySynInstD ''DSH.Rep $ TySynEqn [typ] (deriveRepCons cons)
#else
deriveRep typ cons = TySynInstD ''DSH.Rep [typ] (deriveRepCons cons)
#endif

-- | Derive the representation type 'Rep' for the complete type (all
-- constructors).
deriveRepCons :: [Con] -> Type
deriveRepCons []                   = error errMsgExoticType
-- The representation of a type with only one constructor is the
-- representation of that constructor.
deriveRepCons [c]                  = deriveRepCon c
-- The representation of a type with multiple constructors is a tuple
-- of the representation types for all individual constructors (each
-- wrapped in a list).
deriveRepCons cs | length cs <= 16 = mkTupleType $ map (AppT (ConT ''[]) . deriveRepCon) cs
deriveRepCons _                    = error errMsgTypeTooBroad


-- | Derive the representation type 'Rep' for a single constructor
deriveRepCon :: Con -> Type
deriveRepCon con = case conToTypes con of
  -- A constructor without fields is represented by the empty type
  []                   -> ConT ''()
  -- The representation of a constructor with only one field is the
  -- field type itself.
  [t]                  -> t
  -- Constructors with more fields (up to 16) are represented by a
  -- tuple that contains values for all fields.
  ts | length ts <= 16 -> mkTupleType $ map (AppT (ConT ''DSH.Rep)) ts
  _  | otherwise       -> error errMsgTypeTooBroad

-- Deriving the toExp function of the QA class

deriveToExp :: [Con] -> Q Dec
deriveToExp [] = fail errMsgExoticType
deriveToExp cons = do
  clauses <- sequence (zipWith3 deriveToExpClause (repeat (length cons)) [0 .. ] cons)
  return (FunD 'DSH.toExp clauses)

deriveToExpClause :: Int -- Total number of constructors
                  -> Int -- Index of the constructor
                  -> Con
                  -> Q Clause
deriveToExpClause 0 _ _ = fail errMsgExoticType
deriveToExpClause 1 _ con = do
  (pat1,names1) <- conToPattern con
  exp1 <- deriveToExpMainExp names1
  let body1 = NormalB exp1
  return (Clause [pat1] body1 [])
-- FIXME adapt code for types with multiple constructors to new tuple
-- regime.
deriveToExpClause _n _i _con = $unimplemented
{-
  (pat1,names1) <- conToPattern con
  let exp1 = deriveToExpMainExp names1
  expList1 <- [| DSH.ListE [ $(return exp1) ] |]
  expEmptyList <- [| DSH.ListE [] |]
  let lists = concat [ replicate i expEmptyList
                     , [expList1]
                     , replicate (n - i - 1) expEmptyList]
  let exp2 = foldr1 (AppE . AppE (ConE 'DSH.PairE)) lists
  let body1 = NormalB exp2
  return (Clause [pat1] body1 [])
-}

deriveToExpMainExp :: [Name] -> Q Exp
deriveToExpMainExp []     = return $ ConE 'DSH.UnitE
deriveToExpMainExp [name] = return $ AppE (VarE 'DSH.toExp) (VarE name)
deriveToExpMainExp names  = mkTupConstTerm $ map (AppE (VarE 'DSH.toExp) . VarE) names

-- Deriving to frExp function of the QA class

deriveFrExp :: [Con] -> Q Dec
deriveFrExp cons = do
  clauses <- sequence (zipWith3 deriveFrExpClause (repeat (length cons)) [0 .. ] cons)
  imp     <- impossible
  let lastClause = Clause [WildP] (NormalB imp) []
  return (FunD 'DSH.frExp (clauses ++ [lastClause]))

deriveFrExpClause :: Int -- Total number of constructors
                  -> Int -- Index of the constructor
                  -> Con
                  -> Q Clause
deriveFrExpClause 1 _ con = do
  (_,names1) <- conToPattern con
  let pat1 = deriveFrExpMainPat names1
  let exp1 = foldl AppE
                   (ConE (conToName con))
                   (map (AppE (VarE 'DSH.frExp) . VarE) names1)
  let body1 = NormalB exp1
  return (Clause [pat1] body1 [])
-- FIXME adapt code for types with multiple constructors to new tuple
-- regime.
deriveFrExpClause _n _i _con = $unimplemented
{-
  (_,names1) <- conToPattern con
  let pat1 = deriveFrExpMainPat names1
  let patList1 = ConP 'DSH.ListE [ConP '(:) [pat1,WildP]]
  let lists = replicate i WildP ++ [patList1] ++ replicate (n - i - 1) WildP
  let pat2 = foldr1 (\p1 p2 -> ConP 'DSH.PairE [p1,p2]) lists
  let exp1 = foldl AppE
                   (ConE (conToName con))
                   (map (AppE (VarE 'DSH.frExp) . VarE) names1)
  let body1 = NormalB exp1
  return (Clause [pat2] body1 [])
-}

deriveFrExpMainPat :: [Name] -> Pat
deriveFrExpMainPat [] = ConP 'DSH.UnitE []
deriveFrExpMainPat [name] = VarP name
deriveFrExpMainPat names  = mkTuplePat names

-----------------
-- Deriving TA --
-----------------

deriveTA :: Name -> Q [Dec]
deriveTA name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt name1 tyVarBndrs cons _names) ->
      deriveTyConTA name1 tyVarBndrs cons
    TyConI (NewtypeD _cxt name1 tyVarBndrs con  _names) ->
      deriveTyConTA name1 tyVarBndrs [con]
    _ -> fail errMsgExoticType

deriveTyConTA :: Name -> [TyVarBndr] -> [Con] -> Q [Dec]
deriveTyConTA name tyVarBndrs _cons = do
  roles <- reifyRoles name
  let context       = getContext ''DSH.BasicType roles tyVarBndrs
  let typ           = foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs)
  let instanceHead  = AppT (ConT ''DSH.TA) typ
  return [InstanceD context instanceHead []]

-------------------
-- Deriving View --
-------------------

deriveView :: Name -> Q [Dec]
deriveView name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt name1 tyVarBndrs [con] _names) ->
      deriveTyConView name1 tyVarBndrs con
    TyConI (NewtypeD _cxt name1 tyVarBndrs con  _names) ->
      deriveTyConView name1 tyVarBndrs con
    _ -> fail errMsgExoticType

deriveTyConView :: Name -> [TyVarBndr] -> Con -> Q [Dec]
deriveTyConView name tyVarBndrs con = do
  roles <- reifyRoles name
  let context = getContext ''DSH.QA roles tyVarBndrs
  let typ1 = AppT (ConT ''DSH.Q)
                  (foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs))
  let instanceHead = AppT (ConT ''DSH.View) typ1
  let typs = conToTypes con
  let typ2 = if null typs
                then AppT (ConT ''DSH.Q) (ConT ''())
                else foldl AppT (TupleT (length typs)) (map (AppT (ConT ''DSH.Q)) typs)
#if MIN_VERSION_template_haskell(2,9,0)
  let toViewDecTF = TySynInstD ''DSH.ToView $ TySynEqn [typ1] typ2
#else
  let toViewDecTF = TySynInstD ''DSH.ToView [typ1] typ2
#endif
  viewDec <- deriveToView (length typs)
  return [InstanceD context instanceHead [toViewDecTF, viewDec]]

deriveToView :: Int -> Q Dec
deriveToView n = do
  en <- newName "e"
  let ep = VarP en
  let pat1 = ConP 'DSH.Q [ep]

  body1 <- if n == 1
    then [| DSH.Q $ $(return $ VarE en) |]
    else TupE <$> mapM (\i -> [| DSH.Q $ $(mkTupElemTerm n i (VarE en)) |]) [1..n]

  let clause1 = Clause [pat1] (NormalB body1) []
  return (FunD 'DSH.view [clause1])

-------------------
-- Deriving Elim --
-------------------

deriveElim :: Name -> Q [Dec]
deriveElim name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt name1 tyVarBndrs cons _names) ->
      deriveTyConElim name1 tyVarBndrs cons
    TyConI (NewtypeD _cxt name1 tyVarBndrs con  _names) ->
      deriveTyConElim name1 tyVarBndrs [con]
    _ -> fail errMsgExoticType

deriveTyConElim :: Name -> [TyVarBndr] -> [Con] -> Q [Dec]
deriveTyConElim name tyVarBndrs cons = do
  roles <- reifyRoles name
  resultTyName <- newName "r"
  let resTy = VarT resultTyName
  let ty = foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs)
  let context = nameTyApp ''DSH.QA (resTy) : getContext ''DSH.QA roles tyVarBndrs
  let instanceHead = AppT (AppT (ConT ''DSH.Elim) ty) resTy
  let eliminatorDec = deriveEliminator ty resTy cons
  elimDec <- deriveElimFun cons
  return [InstanceD context instanceHead [eliminatorDec,elimDec]]

-- Deriving the Eliminator type function

deriveEliminator :: Type -> Type -> [Con] -> Dec
deriveEliminator typ resTy cons =
#if MIN_VERSION_template_haskell(2,9,0)
  TySynInstD ''DSH.Eliminator $ TySynEqn [typ,resTy] (deriveEliminatorCons resTy cons)
#else
  TySynInstD ''DSH.Eliminator [typ,resTy] (deriveEliminatorCons resTy cons)
#endif


deriveEliminatorCons :: Type -> [Con] -> Type
deriveEliminatorCons _ []  = error errMsgExoticType
deriveEliminatorCons resTy cs  =
  foldr (AppT . AppT ArrowT . deriveEliminatorCon resTy)
        (AppT (ConT ''DSH.Q) resTy)
        cs

deriveEliminatorCon :: Type -> Con -> Type
deriveEliminatorCon resTy con =
  foldr (AppT . AppT ArrowT . AppT (ConT ''DSH.Q))
        (AppT (ConT ''DSH.Q) resTy)
        (conToTypes con)

-- Deriving the elim function of the Elim type class

deriveElimFun :: [Con] -> Q Dec
deriveElimFun cons = do
  clause1 <- deriveElimFunClause cons
  return (FunD 'DSH.elim [clause1])

deriveElimFunClause :: [Con] -> Q Clause
deriveElimFunClause = $unimplemented
-- deriveElimFunClause cons = do
--   en  <- newName "e"
--   fns <- mapM (\ _ -> newName "f") cons
--   let fes = map VarE fns
--   let pats1 = ConP 'DSH.Q [VarP en] : map VarP fns

--   fes2 <- zipWithM deriveElimToLamExp fes (map (length . conToTypes) cons)

--   let e       = VarE en
--   liste <- [| DSH.ListE $(listE $ deriveElimFunClauseExp (return e) (map return fes2)) |]
--   let concate = AppE (AppE (ConE 'DSH.AppE) (ConE 'F.Concat)) liste
--   let heade   = AppE (AppE (ConE 'DSH.AppE) (ConE 'F.Head)) concate
--   let qe      = AppE (ConE 'DSH.Q) heade
--   return (Clause pats1 (NormalB qe) [])

-- deriveElimToLamExp :: Exp -> Int -> Q Exp
-- deriveElimToLamExp f 0 =
--   return (AppE (VarE 'const) (AppE (VarE 'DSH.unQ) f))
-- deriveElimToLamExp f 1 = do
--   xn <- newName "x"
--   let xe = VarE xn
--   let xp = VarP xn
--   let qe = AppE (ConE 'DSH.Q) xe
--   let fappe = AppE f qe
--   let unqe = AppE (VarE 'DSH.unQ) fappe
--   return (LamE [xp] unqe)
-- deriveElimToLamExp f n = do
--   xn <- newName "x"
--   let xe = VarE xn
--   let xp = VarP xn
--   let fste = AppE (AppE (ConE 'DSH.AppE) (ConE 'F.Fst)) xe
--   let snde = AppE (AppE (ConE 'DSH.AppE) (ConE 'F.Snd)) xe
--   let qe = AppE (ConE 'DSH.Q) fste
--   let fappe = AppE f qe
--   f' <- deriveElimToLamExp fappe (n - 1)
--   return (LamE [xp] (AppE f' snde))

-- deriveElimFunClauseExp :: Q Exp -> [Q Exp] -> [Q Exp]
-- deriveElimFunClauseExp _ [] = error errMsgExoticType
-- deriveElimFunClauseExp e [f] = [ [| DSH.ListE [$f $e] |] ]
-- deriveElimFunClauseExp e fs = go e fs
--   where
--   go :: Q Exp -> [Q Exp] -> [Q Exp]
--   go _ []  = error errMsgExoticType
--   -- FIXME PairE
--   go e1 [f1] = do
--     [ [| DSH.AppE F.Map (DSH.TupleConstE (DSH.Tuple2E (DSH.LamE $f1) $e1)) |] ]
--   go e1 (f1 : fs1) = do
--     let mape = [| DSH.AppE F.Map (DSH.TupleConstE (DSH.Tuple2E (DSH.LamE $f1) (DSH.AppE F.Fst $e1))) |]
--     let snde = [| DSH.AppE F.Snd $e1 |]
--     mape : go snde fs1

---------------------------------
-- Deriving Smart Constructors --
---------------------------------

deriveSmartConstructors :: Name -> Q [Dec]
deriveSmartConstructors name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt typConName tyVarBndrs cons _names) -> do
      decss <- zipWithM (deriveSmartConstructor typConName tyVarBndrs (length cons))
                        [0 .. ]
                        cons
      return (concat decss)
    TyConI (NewtypeD _cxt typConName tyVarBndrs con  _names) ->
      deriveSmartConstructor typConName tyVarBndrs 1 0 con
    _ -> fail errMsgExoticType

deriveSmartConstructor :: Name -> [TyVarBndr] -> Int -> Int -> Con -> Q [Dec]
deriveSmartConstructor typConName tyVarBndrs n i con = do
  let smartConName = toSmartConName (conToName con)

  let boundTyps = map (VarT . tyVarBndrToName) tyVarBndrs

  let resTyp = AppT (ConT ''DSH.Q) (foldl AppT (ConT typConName) boundTyps)

  let smartConContext = map (nameTyApp ''DSH.QA) boundTyps

  let smartConTyp = foldr (AppT . AppT ArrowT . AppT (ConT ''DSH.Q))
                          resTyp
                          (conToTypes con)

  let smartConDec = SigD smartConName (ForallT tyVarBndrs smartConContext smartConTyp)

  ns <- mapM (\_ -> newName "e") (conToTypes con)
  let es = map VarE ns

  let smartConPat = map (ConP 'DSH.Q . return . VarP) ns

  -- FIXME PairE -> TupleE
  smartConExp <- if null es
                 then return $ ConE 'DSH.UnitE
                 else mkTupConstTerm es
  smartConBody <- deriveSmartConBody n i smartConExp
  let smartConClause = Clause smartConPat (NormalB smartConBody) []

  let funDec = FunD smartConName [smartConClause]

  return [smartConDec,funDec]

deriveSmartConBody :: Int -- Total number of constructors
                   -> Int -- Index of the constructor
                   -> Exp
                   -> Q Exp
deriveSmartConBody 0 _ _ = fail errMsgExoticType
deriveSmartConBody 1 _ e = return (AppE (ConE 'DSH.Q) e)
deriveSmartConBody n i e = do
  listExp <- [| DSH.ListE [ $(return e) ] |]
  emptyListExp <- [| DSH.ListE [] |]
  let lists = concat [ replicate i emptyListExp
                     , [listExp]
                     , replicate (n - i - 1) emptyListExp
                     ]
  tupleExp <- mkTupConstTerm lists
  return $ AppE (ConE 'DSH.Q) tupleExp

toSmartConName :: Name -> Name
toSmartConName name1 = case nameBase name1 of
  "()"                -> mkName "unit"
  '(' : cs            -> mkName ("tuple" ++ show (length (filter (== ',') cs) + 1))
  c : cs | isAlpha c  -> mkName (toLower c : cs)
  cs                  -> mkName (':' : cs)

----------------------------------------
-- Generating lifted record selectors --
----------------------------------------

{-

For a record declaration like

data R = R { a :: Integer, b :: Text }

we generate the following lifted selectors:

aQ :: Q R -> Q Integer
aQ (view -> (a, _)) = a

bQ :: Q R -> Q Text
bQ (view -> (_, b)) = b

-}

-- | Create lifted record selectors
generateTableSelectors :: Name -> Q [Dec]
generateTableSelectors name = do
  info <- reify name
  case info of
    TyConI (DataD typCxt typName typVars [RecC _ fields] _) -> go typCxt typName typVars fields
    TyConI (NewtypeD typCxt typName typVars (RecC _ fields) _) -> go typCxt typName typVars fields
    _ -> fail errMsgBaseRecCons
 where
  go typCxt typName typVars fields = concat <$> mapM instSelectors fields
   where
    fieldNames    = map (\(f, _, _) -> f) fields
    instSelectors = generateTableSelector typCxt typName typVars fieldNames

generateTableSelector :: Cxt -> Name -> [TyVarBndr] -> [Name] -> VarStrictType -> Q [Dec]
generateTableSelector typeCxt typeName typeVars allFieldNames (fieldName, _strict, typ) = do
  let selName = case fieldName of
                  Name (OccName n) _ -> mkName $ n ++ "Q"

  let nameWithVars = foldl AppT (ConT typeName) $ map (VarT . tyVarBndrToName) typeVars

  let selType = ForallT typeVars typeCxt
                  (AppT (AppT ArrowT (AppT (ConT ''DSH.Q) nameWithVars))
                    (AppT (ConT ''DSH.Q) typ))
      sigDec  = SigD selName selType

  fieldVarName <- newName "x"
  let projectField f | f == fieldName = VarP fieldVarName
      projectField _                  = WildP

      tupPat   = map projectField allFieldNames

      argPat   = ViewP (VarE 'DSH.view) (TupP tupPat)

      bodyExp  = NormalB $ VarE fieldVarName

      funDec   = FunD selName [Clause [argPat] bodyExp []]


  return [sigDec, funDec]

-- Helper Functions


-- | From a list of operand patterns, construct a DSH tuple term
-- pattern.
-- @
-- TupleE (Tuple3E a b) -> ...
-- @
mkTuplePat :: [Name] -> Pat
mkTuplePat names = ConP 'DSH.TupleConstE
                        [ConP (innerConst "" $ length names) (map VarP names)]

-- | Generate a (flat) tuple type from the list of element types.
mkTupleType :: [Type] -> Type
mkTupleType ts = foldl' AppT (TupleT $ length ts) ts

-- | Return the types of all fields of a constructor.
conToTypes :: Con -> [Type]
conToTypes (NormalC _name strictTypes) = map snd strictTypes
conToTypes (RecC _name varStrictTypes) = map (\(_,_,t) -> t) varStrictTypes
conToTypes (InfixC st1 _name st2) = [snd st1,snd st2]
conToTypes (ForallC _tyVarBndrs _cxt con) = conToTypes con

tyVarBndrToName :: TyVarBndr -> Name
tyVarBndrToName (PlainTV name) = name
tyVarBndrToName (KindedTV name _kind) = name

-- | For a given constructor, create a pattern that matches the
-- constructor and binds all fields to the names returned.
conToPattern :: Con -> Q (Pat,[Name])
conToPattern (NormalC name strictTypes) = do
  ns <- mapM (\ _ -> newName "x") strictTypes
  return (ConP name (map VarP ns),ns)
conToPattern (RecC name varStrictTypes) = do
  ns <- mapM (\ _ -> newName "x") varStrictTypes
  return (ConP name (map VarP ns),ns)
conToPattern (InfixC st1 name st2) = do
  ns <- mapM (\ _ -> newName "x") [st1,st2]
  return (ConP name (map VarP ns),ns)
conToPattern (ForallC _tyVarBndr _cxt con) = conToPattern con

conToName :: Con -> Name
conToName (NormalC name _)  = name
conToName (RecC name _)     = name
conToName (InfixC _ name _) = name
conToName (ForallC _ _ con) = conToName con

countConstructors :: Name -> Q Int
countConstructors name = do
  info <- reify name
  case info of
    TyConI (DataD    _ _ _ cons _)  -> return (length cons)
    TyConI (NewtypeD {})            -> return 1
    _ -> fail errMsgExoticType

getContext :: Name -> [Role] -> [TyVarBndr] -> [Type]
getContext klass roles tyVarBndrs = flip mapMaybe (zip roles tyVarBndrs) $
  \(role, tv) -> case role of
    PhantomR -> Nothing
    _ -> Just (nameTyApp klass (VarT (tyVarBndrToName tv)))

-- Error messages

errMsgExoticType :: String
errMsgExoticType =
  "Automatic derivation of DSH related type class instances only works for Haskell 98\n"
  ++ "types. Derivation of View patterns is only supported for single-constructor data\n"
  ++ "types."

errMsgBaseRecCons :: String
errMsgBaseRecCons =
  "Generation of lifted record selectors is only supported for records of base types."

errMsgTypeTooBroad :: String
errMsgTypeTooBroad =
  "DSH currently supports data types with up to 16 constructors and in which \n"
  ++ "all constructors have up to 16 fields."
