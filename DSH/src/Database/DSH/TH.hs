{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.TH ( deriveDSH
                       , deriveQA
                       , deriveTupleRangeQA
                       , deriveView
                       , deriveTupleRangeView
                       , deriveElim
                       , deriveSmartConstructors
                       , deriveTupleRangeSmartConstructors
                       ) where

import qualified Database.DSH.Internals  as DSH
import qualified Database.DSH.Impossible as DSH

import Language.Haskell.TH
import Control.Monad
import Data.Char

-----------------------------------------
-- Deriving all DSH-relevant instances --
-----------------------------------------

deriveDSH :: Name -> Q [Dec]
deriveDSH n = do
  qaDecs    <- deriveQA n
  elimDecs  <- deriveElim n
  cc        <- countConstructors n
  viewDecs  <- if cc == 1
                  then deriveView n
                  else return []
  scDecs    <- deriveSmartConstructors n
  return (qaDecs ++ elimDecs ++ viewDecs ++ scDecs)

-----------------
-- Deriving QA --
-----------------

deriveQA :: Name -> Q [Dec]
deriveQA name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt name1 tyVarBndrs cons _names) ->
      deriveTyConQA name1 tyVarBndrs cons
    TyConI (NewtypeD _cxt name1 tyVarBndrs con  _names) ->
      deriveTyConQA name1 tyVarBndrs [con]
    _ -> fail errMsgExoticType

deriveTupleRangeQA :: Int -> Int -> Q [Dec]
deriveTupleRangeQA x y = fmap concat (mapM (deriveQA . tupleTypeName) [x .. y])

deriveTyConQA :: Name -> [TyVarBndr] -> [Con] -> Q [Dec]
deriveTyConQA name tyVarBndrs cons = do
  let context       = map (\tv -> ClassP ''DSH.QA [VarT (tyVarBndrToName tv)])
                          tyVarBndrs
  let typ           = foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs)
  let instanceHead  = AppT (ConT ''DSH.QA) typ
  let repDec        = deriveRep typ cons
  toExpDec <- deriveToExp cons
  frExpDec <- deriveFrExp cons
  return [InstanceD context instanceHead [repDec,toExpDec,frExpDec]]

-- Deriving the Rep type function

deriveRep :: Type -> [Con] -> Dec
deriveRep typ cons = TySynInstD ''DSH.Rep [typ] (deriveRepCons cons)

deriveRepCons :: [Con] -> Type
deriveRepCons []  = error errMsgExoticType
deriveRepCons [c] = deriveRepCon c
deriveRepCons cs  = foldr1 (AppT . AppT (ConT ''(,)))
                           (map (AppT (ConT ''[]) . deriveRepCon) cs)

deriveRepCon :: Con -> Type
deriveRepCon con = case conToTypes con of
  [] -> ConT ''()
  ts -> foldr1 (AppT . AppT (ConT ''(,)))
               (map (AppT (ConT ''DSH.Rep)) ts)

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
  let exp1 = deriveToExpMainExp names1
  let body1 = NormalB exp1
  return (Clause [pat1] body1 [])
deriveToExpClause n i con = do
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

deriveToExpMainExp :: [Name] -> Exp
deriveToExpMainExp []     = ConE 'DSH.UnitE
deriveToExpMainExp [name] = AppE (VarE 'DSH.toExp) (VarE name)
deriveToExpMainExp names  = foldr1 (AppE . AppE (ConE 'DSH.PairE))
                                   (map (AppE (VarE 'DSH.toExp) . VarE) names)
-- Deriving to frExp function of the QA class

deriveFrExp :: [Con] -> Q Dec
deriveFrExp cons = do
  clauses <- sequence (zipWith3 deriveFrExpClause (repeat (length cons)) [0 .. ] cons)
  imp <- DSH.impossible
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
deriveFrExpClause n i con = do
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

deriveFrExpMainPat :: [Name] -> Pat
deriveFrExpMainPat [] = ConP 'DSH.UnitE []
deriveFrExpMainPat [name] = VarP name
deriveFrExpMainPat names  = foldr1 (\p1 p2 -> ConP 'DSH.PairE [p1,p2]) (map VarP names)

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

deriveTupleRangeView :: Int -> Int -> Q [Dec]
deriveTupleRangeView x y = fmap concat (mapM (deriveView . tupleTypeName) [x .. y])

deriveTyConView :: Name -> [TyVarBndr] -> Con -> Q [Dec]
deriveTyConView name tyVarBndrs con = do
  let context = map (\tv -> ClassP ''DSH.QA [VarT (tyVarBndrToName tv)]) tyVarBndrs
  let typ1 = AppT (ConT ''DSH.Q)
                  (foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs))
  let instanceHead = AppT (ConT ''DSH.View) typ1
  let typs = conToTypes con
  let typ2 = if null typs
                then AppT (ConT ''DSH.Q) (ConT ''())
                else foldl AppT (TupleT (length typs)) (map (AppT (ConT ''DSH.Q)) typs)
  let toViewDecTF = TySynInstD ''DSH.ToView [typ1] typ2
  viewDec <- deriveToView (length typs)
  return [InstanceD context instanceHead [toViewDecTF, viewDec]]

deriveToView :: Int -> Q Dec
deriveToView n = do
  en <- newName "e"
  let ep = VarP en
  let pat1 = ConP 'DSH.Q [ep]

  let fAux 0  e1 = [AppE (ConE 'DSH.Q) e1]
      fAux 1  e1 = [AppE (ConE 'DSH.Q) e1]
      fAux n1 e1 = let fste = AppE (AppE (ConE 'DSH.AppE) (ConE 'DSH.Fst)) e1
                       snde = AppE (AppE (ConE 'DSH.AppE) (ConE 'DSH.Snd)) e1
                   in  AppE (ConE 'DSH.Q) fste : fAux (n1 - 1) snde

  let body1 = TupE (fAux n (VarE en))
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
  resultTyName <- newName "r"
  let resTy = VarT resultTyName
  let ty = foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs)
  let context = ClassP ''DSH.QA [resTy] :
                map (\tv -> ClassP ''DSH.QA [VarT (tyVarBndrToName tv)]) tyVarBndrs
  let instanceHead = AppT (AppT (ConT ''DSH.Elim) ty) resTy
  let eliminatorDec = deriveEliminator ty resTy cons
  elimDec <- deriveElimFun cons
  return [InstanceD context instanceHead [eliminatorDec,elimDec]]

-- Deriving the Eliminator type function

deriveEliminator :: Type -> Type -> [Con] -> Dec
deriveEliminator typ resTy cons =
  TySynInstD ''DSH.Eliminator [typ,resTy] (deriveEliminatorCons resTy cons)

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
deriveElimFunClause cons = do
  en  <- newName "e"
  fns <- mapM (\ _ -> newName "f") cons
  let fes = map VarE fns
  let pats1 = ConP 'DSH.Q [VarP en] : map VarP fns

  fes2 <- zipWithM deriveElimToLamExp fes (map (length . conToTypes) cons)

  let e       = VarE en
  let liste   = AppE (ConE 'DSH.ListE) (ListE (deriveElimFunClauseExp e fes2))
  let concate = AppE (AppE (ConE 'DSH.AppE) (ConE 'DSH.Concat)) liste
  let heade   = AppE (AppE (ConE 'DSH.AppE) (ConE 'DSH.Head)) concate
  let qe      = AppE (ConE 'DSH.Q) heade
  return (Clause pats1 (NormalB qe) [])

deriveElimToLamExp :: Exp -> Int -> Q Exp
deriveElimToLamExp f 0 =
  return (AppE (VarE 'const) (AppE (VarE 'DSH.unQ) f))
deriveElimToLamExp f 1 = do
  xn <- newName "x"
  let xe = VarE xn
  let xp = VarP xn
  let qe = AppE (ConE 'DSH.Q) xe
  let fappe = AppE f qe
  let unqe = AppE (VarE 'DSH.unQ) fappe
  return (LamE [xp] unqe)
deriveElimToLamExp f n = do
  xn <- newName "x"
  let xe = VarE xn
  let xp = VarP xn
  let fste = AppE (AppE (ConE 'DSH.AppE) (ConE 'DSH.Fst)) xe
  let snde = AppE (AppE (ConE 'DSH.AppE) (ConE 'DSH.Snd)) xe
  let qe = AppE (ConE 'DSH.Q) fste
  let fappe = AppE f qe
  f' <- deriveElimToLamExp fappe (n - 1)
  return (LamE [xp] (AppE f' snde))

deriveElimFunClauseExp :: Exp -> [Exp] -> [Exp]
deriveElimFunClauseExp _ [] = error errMsgExoticType
deriveElimFunClauseExp e [f] = [AppE (ConE 'DSH.ListE) (ListE [AppE f e])]
deriveElimFunClauseExp e fs = go e fs
  where
  go :: Exp -> [Exp] -> [Exp]
  go _ []  = error errMsgExoticType
  go e1 [f1] =
    let paire = AppE (AppE (ConE 'DSH.PairE) (AppE (ConE 'DSH.LamE) f1)) e1
    in  [AppE (AppE (ConE 'DSH.AppE) (ConE 'DSH.Map)) paire]
  go e1 (f1 : fs1) =
    let fste  = AppE (AppE (ConE 'DSH.AppE) (ConE 'DSH.Fst)) e1
        snde  = AppE (AppE (ConE 'DSH.AppE) (ConE 'DSH.Snd)) e1
        paire = AppE (AppE (ConE 'DSH.PairE) (AppE (ConE 'DSH.LamE) f1)) fste
        mape  = AppE (AppE (ConE 'DSH.AppE) (ConE 'DSH.Map)) paire
    in  mape : go snde fs1

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

deriveTupleRangeSmartConstructors :: Int -> Int -> Q [Dec]
deriveTupleRangeSmartConstructors x y =
  fmap concat (mapM (deriveSmartConstructors . tupleTypeName) [x .. y])

deriveSmartConstructor :: Name -> [TyVarBndr] -> Int -> Int -> Con -> Q [Dec]
deriveSmartConstructor typConName tyVarBndrs n i con = do
  let smartConName = toSmartConName (conToName con)
  
  let boundTyps = map (VarT . tyVarBndrToName) tyVarBndrs

  let resTyp = AppT (ConT ''DSH.Q) (foldl AppT (ConT typConName) boundTyps)

  let smartConContext = map (ClassP ''DSH.QA . return) boundTyps
  
  let smartConTyp = foldr (AppT . AppT ArrowT . AppT (ConT ''DSH.Q))
                          resTyp
                          (conToTypes con)
  
  let smartConDec = SigD smartConName (ForallT tyVarBndrs smartConContext smartConTyp)

  ns <- mapM (\_ -> newName "e") (conToTypes con)
  let es = map VarE ns
  
  let smartConPat = map (ConP 'DSH.Q . return . VarP) ns
  
  let smartConExp = if null es
                       then (ConE 'DSH.UnitE)
                       else foldr1 (AppE . AppE (ConE 'DSH.PairE)) es
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
  let pairExp = foldr1 (AppE . AppE (ConE 'DSH.PairE)) lists
  return (AppE (ConE 'DSH.Q) pairExp)

toSmartConName :: Name -> Name
toSmartConName name1 = case nameBase name1 of
  "()"                -> mkName "unit"
  '(' : cs            -> mkName ("tuple" ++ show (length (filter (== ',') cs) + 1))
  c : cs | isAlpha c  -> mkName (toLower c : cs)
  cs                  -> mkName (':' : cs)

-- Helper Functions

conToTypes :: Con -> [Type]
conToTypes (NormalC _name strictTypes) = map snd strictTypes
conToTypes (RecC _name varStrictTypes) = map (\(_,_,t) -> t) varStrictTypes
conToTypes (InfixC st1 _name st2) = [snd st1,snd st2]
conToTypes (ForallC _tyVarBndrs _cxt con) = conToTypes con

tyVarBndrToName :: TyVarBndr -> Name
tyVarBndrToName (PlainTV name) = name
tyVarBndrToName (KindedTV name _kind) = name

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
conToName (NormalC name _) = name
conToName (RecC name _) = name
conToName (InfixC _ name _) = name
conToName (ForallC _ _ con)	= conToName con

countConstructors :: Name -> Q Int
countConstructors name = do
  info <- reify name
  case info of
    TyConI (DataD    _ _ _ cons _)  -> return (length cons)
    TyConI (NewtypeD {})            -> return 1
    _ -> fail errMsgExoticType

-- Error messages

errMsgExoticType :: String
errMsgExoticType =
  "Automatic derivation of DSH related type class instances only works for Haskell 98\
   \ types. Derivation of View patters is only supported for single-constructor data\
   \ types."
