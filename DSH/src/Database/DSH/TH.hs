module Database.DSH.TH (deriveQA,deriveTupleRangeQA) where

import qualified Database.DSH.Impossible as DSH
import qualified Database.DSH.Data as DSH

import Language.Haskell.TH

-- Deriving QA

deriveQA :: Name -> Q [Dec]
deriveQA name = do
  info <- reify name
  case info of
    TyConI (DataD    _cxt name1 tyVarBndrs cons _names) -> deriveTyConQA name1 tyVarBndrs cons
    TyConI (NewtypeD _cxt name1 tyVarBndrs con  _names) -> deriveTyConQA name1 tyVarBndrs [con]
    _ -> fail errMsgExoticType

deriveTyConQA :: Name -> [TyVarBndr] -> [Con] -> Q [Dec]
deriveTyConQA name tyVarBndrs cons = do
  let context = map (\tv -> ClassP ''DSH.QA [VarT (tyVarBndrToName tv)]) tyVarBndrs
  let typ = foldl AppT (ConT name) (map (VarT . tyVarBndrToName) tyVarBndrs)
  let instanceHead = AppT (ConT ''DSH.QA) typ
  let repDec = deriveRep typ cons
  toExpDec <- deriveToExp cons
  frExpDex <- deriveFrExp cons
  return [InstanceD context instanceHead [repDec,toExpDec,frExpDex]]

deriveTupleRangeQA :: Int -> Int -> Q [Dec]
deriveTupleRangeQA x y = fmap concat (mapM (deriveQA . tupleTypeName) [x .. y])

-- Derive the Rep type function

deriveRep :: Type -> [Con] -> Dec
deriveRep typ cons = TySynInstD ''DSH.Rep [typ] (deriveRepCons cons)

deriveRepCons :: [Con] -> Type
deriveRepCons []  = error errMsgExoticType
deriveRepCons [c] = deriveRepCon c
deriveRepCons cs  = foldr1 (AppT . AppT (ConT ''(,))) (map (AppT (ConT ''[]) . deriveRepCon) cs)

deriveRepCon :: Con -> Type
deriveRepCon con = case conToTypes con of
  [] -> ConT ''()
  ts -> foldr1 (AppT . AppT (ConT ''(,))) (map (AppT (ConT ''DSH.Rep)) ts)

-- Derive the toExp function of the QA class

deriveToExp :: [Con] -> Q Dec
deriveToExp [] = fail errMsgExoticType
deriveToExp cons = do
  clauses <- sequence (zipWith3 deriveToExpClause (repeat (length cons)) [0 .. ] cons)
  return (FunD 'DSH.toExp clauses)

deriveToExpClause :: Int -> Int -> Con -> Q Clause
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
  let lists = replicate i expEmptyList ++ [expList1] ++ replicate (n - i - 1) expEmptyList
  let exp2 = foldr1 (AppE . AppE (ConE 'DSH.PairE)) lists
  let body1 = NormalB exp2
  return (Clause [pat1] body1 [])

deriveToExpMainExp :: [Name] -> Exp
deriveToExpMainExp []     = ConE 'DSH.UnitE
deriveToExpMainExp [name] = AppE (VarE 'DSH.toExp) (VarE name)
deriveToExpMainExp names  = foldr1 (AppE . AppE (ConE 'DSH.PairE))
                                   (map (AppE (VarE 'DSH.toExp) . VarE) names)
-- Derive to frExp function of the QA class

deriveFrExp :: [Con] -> Q Dec
deriveFrExp cons = do
  clauses <- sequence (zipWith3 deriveFrExpClause (repeat (length cons)) [0 .. ] cons)
  imp <- DSH.impossible
  let lastClause = Clause [WildP] (NormalB imp) []
  return (FunD 'DSH.frExp (clauses ++ [lastClause]))

deriveFrExpClause :: Int -> Int -> Con -> Q Clause
deriveFrExpClause 1 _ con = do
  (_,names1) <- conToPattern con
  let pat1 = deriveFrExpMainPat names1
  let exp1 = foldl AppE (ConE (conToName con)) (map (AppE (VarE 'DSH.frExp) . VarE) names1)
  let body1 = NormalB exp1
  return (Clause [pat1] body1 [])
deriveFrExpClause n i con = do
  (_,names1) <- conToPattern con
  let pat1 = deriveFrExpMainPat names1
  let patList1 = ConP 'DSH.ListE [ConP '(:) [pat1,WildP]]
  let lists = replicate i WildP ++ [patList1] ++ replicate (n - i - 1) WildP
  let pat2 = foldr1 (\p1 p2 -> ConP 'DSH.PairE [p1,p2]) lists
  let exp1 = foldl AppE (ConE (conToName con)) (map (AppE (VarE 'DSH.frExp) . VarE) names1)
  let body1 = NormalB exp1
  return (Clause [pat2] body1 [])

deriveFrExpMainPat :: [Name] -> Pat
deriveFrExpMainPat [] = ConP 'DSH.UnitE []
deriveFrExpMainPat [name] = VarP name
deriveFrExpMainPat names  = foldr1 (\p1 p2 -> ConP 'DSH.PairE [p1,p2]) (map VarP names)

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

-- Error messages

errMsgExoticType :: String
errMsgExoticType =  "Derivation of QA is only possible for Haskell 98 types types."