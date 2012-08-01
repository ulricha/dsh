-- | DSH compiler module exposes the function fromQ that can be used to
-- execute DSH programs on a database. It transform the DSH program into
-- FerryCore which is then translated into SQL (through a table algebra). The SQL
-- code is executed on the database and then processed to form a Haskell value.

{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, ScopedTypeVariables, GADTs #-}

module Database.DSH.Compiler (fromQ, debugPlan, debugCore, debugPlanOpt, debugSQL, debugCoreDot) where

import Database.DSH.Data as D
import Database.DSH.Impossible (impossible)
import Database.DSH.CSV (csvImport)

import Database.DSH.Compile as C

import Database.Ferry.SyntaxTyped  as F
import Database.Ferry.Compiler

import qualified Data.Map as M
import Data.Char
import Database.HDBC
import Data.Convertible

import Control.Monad.State
import Control.Applicative

import Data.Text (unpack)

import Data.List (nub)
import qualified Data.List as L

import Data.Generics (listify)

{-
N monad, version of the state monad that can provide fresh variable names.
-}
type N conn = StateT (conn, Int, M.Map String [(String, (FType -> Bool))]) IO

-- | Provide a fresh identifier name during compilation
freshVar :: N conn Int
freshVar = do
             (c, i, env) <- get
             put (c, i + 1, env)
             return i

-- | Get from the state the connection to the database                
getConnection :: IConnection conn => N conn conn
getConnection = do
                 (c, _, _) <- get
                 return c

-- | Lookup information that describes a table. If the information is 
-- not present in the state then the connection is used to retrieve the
-- table information from the Database.
tableInfo :: IConnection conn => String -> N conn [(String, (FType -> Bool))]
tableInfo t = do
               (c, i, env) <- get
               case M.lookup t env of
                     Nothing -> do
                                 inf <- lift $ getTableInfo c t
                                 put (c, i, M.insert t inf env)
                                 return inf                                      
                     Just v -> return v

-- | Turn a given integer into a variable beginning with prefix "__fv_"                    
prefixVar :: Int -> String
prefixVar = ((++) "__fv_") . show
     
-- | Execute the transformation computation. During
-- compilation table information can be retrieved from
-- the database, therefor the result is wrapped in the IO
-- Monad.      
runN :: IConnection conn => conn -> N conn a -> IO a
runN c  = liftM fst . flip runStateT (c, 1, M.empty)
            
-- * Convert DB queries into Haskell values

-- | Execute the query on the database
fromQ :: forall a conn. (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c a = evaluate c a >>= (return . fromNorm)


-- | Convert the query into unoptimised algebraic plan
debugPlan :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugPlan = doCompile

-- | Convert the query into optimised algebraic plan
debugPlanOpt :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugPlanOpt q c = do
                    p <- doCompile q c
                    (C.Algebra r) <- algToAlg ((C.Algebra p)::AlgebraXML a)
                    return r

debugCore :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugCore c a = do
                     core <- runN c $ transformE $ qToExp a
                     return $ show core


debugCoreDot :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugCoreDot c a = do
                        core <- runN c $ transformE $ qToExp a
                        return $ (\(Right d) -> d) $ dot core

-- | Convert the query into SQL
debugSQL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugSQL q c = do
                p <- doCompile q c
                (C.SQL r) <- algToSQL ((C.Algebra p)::AlgebraXML a)
                return r

-- | evaluate compiles the given Q query into an executable plan, executes this and returns 
-- the result as norm. For execution it uses the given connection. If the boolean flag is set
-- to true it outputs the intermediate algebraic plan to disk.
evaluate :: forall a. forall conn. (QA a, IConnection conn)
         =>  conn
         -> Q a
         -> IO (Norm a)
evaluate c q = do
                  algPlan' <- doCompile c q
                  let algPlan = ((C.Algebra algPlan') :: AlgebraXML a)
                  n <- executePlan c algPlan
                  disconnect c
                  return n

-- | Transform a query into an algebraic plan.                   
doCompile :: (QA a, IConnection conn) => conn -> Q a -> IO String
doCompile c a = do 
                        core <- runN c $ transformE $ qToExp a
                        return $ typedCoreToAlgebra core

-- | Transform the Query into a ferry core program.
transformE :: (IConnection conn, QA a) => Exp a -> N conn CoreExpr
transformE _ = error "transformE: Not implemented"
transformE (UnitE ) = return $ Constant ([] :=> int) $ CInt 1
transformE (BoolE b) = return $ Constant ([] :=> bool) $ CBool b
transformE (CharE c) = return $ Constant ([] :=> string) $ CString [c] 
transformE (IntegerE i) = return $ Constant ([] :=> int) $ CInt i
transformE (DoubleE d) = return $ Constant ([] :=> float) $ CFloat d
transformE (TextE t) = return $ Constant ([] :=> string) $ CString $ unpack t
transformE ((PairE e1 e2) :: Exp t) = do
                            let ty = reify (undefined :: t)
                            c1 <- transformE e1
                            c2 <- transformE e2
                            return $ Rec ([] :=> transformTy ty) [RecElem (typeOf c1) "1" c1, RecElem (typeOf c2) "2" c2] 
transformE ((ListE es) :: Exp t) = let ty = reify (undefined :: t)
                                       qt = ([] :=> transformTy ty) 
                                    in foldr (\h t -> F.Cons qt h t) (Nil qt) <$> mapM transformE es
transformE ((App1E f1 e1) :: Exp t) = do
                                      let ty = reify (undefined :: t)
                                      let tr = transformTy ty
                                      e1' <- transformArg e1
                                      let (_ :=> ta) = typeOf e1'
                                      return $ App ([] :=> tr) (transformF f1 (ta .-> tr)) e1'
transformE (AppH2E Span f e) = transformE $ PairE (AppH2E TakeWhile f e) (AppH2E DropWhile f e)
transformE (AppH2E Break (Lam1E f) e) = let notF = Lam1E (\x -> App1E Not (f x)) 
                                         in transformE $ AppH2E Span notF e
transformE ((AppH2E GroupWith (gfn :: Exp (ta -> rt)) (e:: Exp el)) :: Exp t) = do
                                                let ty = reify (undefined :: [[el]])
                                                let tel = reify (undefined :: el)
                                                let tr = transformTy ty
                                                fn' <- transformL1Arg gfn
                                                let (_ :=> tfn@(FFn _ rt)) = typeOf fn'
                                                let gtr = list $ rec [(RLabel "1", rt), (RLabel "2", transformTy $ ListT tel)]
                                                e' <- transformArg e
                                                let (_ :=> te) = typeOf e'
                                                fv <- transformL1Arg ((Lam1E id) :: Exp (el -> el))
                                                snd' <- transformL1Arg ((Lam1E (\x -> App1E Snd x) ) :: (Exp ((rt, [el]) -> [el])))
                                                let (_ :=> sndTy) = typeOf snd'
                                                let (_ :=> tfv) = typeOf fv
                                                return $ App ([] :=> tr)
                                                            (App ([] :=> gtr .-> tr) (Var ([] :=> sndTy .-> gtr .-> tr) "map") snd') 
                                                            (ParExpr ([] :=> gtr) $ App ([] :=> gtr)
                                                                (App ([] :=> te .-> gtr)
                                                                    (App ([] :=> tfn .-> te .-> gtr) (Var ([] :=> tfv .-> tfn .-> te .-> gtr) "groupWith") fv)
                                                                    fn'
                                                                )
                                                                e')
{-
transformE (AppE2 D.Cons e1 e2 _) = do
                                            e1' <- transformE e1
                                            e2' <- transformE e2
                                            let (_ :=> t) = typeOf e1'
                                            return $ F.Cons ([] :=> list t) e1' e2'
transformE (AppE2 Append e1 e2 t) = transformE (AppE1 Concat (ListE [e1, e2] (ListT t)) t)
transformE (AppE2 Any f e _) = transformE $ AppE1 Or (AppE2 Map f e $ ListT BoolT) BoolT
transformE (AppE2 All f e _) = transformE $ AppE1 And (AppE2 Map f e $ ListT BoolT) BoolT
transformE (AppE2 Snoc e1 e2 t) = transformE (AppE2 Append e1 (ListE [e2] t) t)
transformE (AppE2 f2 e1 e2 ty) = do
                                        let tr = transformTy ty
                                        case elem f2 [Add, Sub, Mul, Div, Equ, Lt, Lte, Gte, Gt, Conj, Disj] of
                                            True  -> do
                                                      e1' <- transformE e1
                                                      e2' <- transformE e2
                                                      return $ BinOp ([] :=> tr) (transformOp f2) e1' e2'
                                            False -> do
                                                      e1' <- transformArg e1
                                                      e2' <- transformArg e2
                                                      let (_ :=> ta1) = typeOf e1'
                                                      let (_ :=> ta2) = typeOf e2'
                                                      return $ App ([] :=> tr) 
                                                                (App ([] :=> ta2 .-> tr) (transformF f2 (ta1 .-> ta2 .-> tr)) e1')
                                                                e2'
transformE (AppE3 Cond e1 e2 e3 _) = do
                                             e1' <- transformE e1
                                             e2' <- transformE e2
                                             e3' <- transformE e3
                                             let (_ :=> t) = typeOf e2'
                                             return $ If ([] :=> t) e1' e2' e3'
transformE (AppE3 f3 e1 e2 e3 ty) = do
                                           let tr = transformTy ty
                                           e1' <- transformArg e1
                                           e2' <- transformArg e2
                                           e3' <- transformArg e3
                                           let (_ :=> ta1) = typeOf e1'
                                           let (_ :=> ta2) = typeOf e2'
                                           let (_ :=> ta3) = typeOf e3'
                                           return $ App ([] :=> tr)
                                                        (App ([] :=> ta3 .-> tr)
                                                             (App ([] :=> ta2 .-> ta3 .-> tr) (transformF f3 (ta1 .-> ta2 .-> ta3 .-> tr)) e1')
                                                             e2')
                                                        e3'
transformE (VarE i ty) = return $ Var ([] :=> transformTy ty) $ prefixVar i
transformE (TableE (TableCSV filepath) ty) = do
                                              norm1 <- lift (csvImport filepath ty)
                                              transformE (convert norm1)
-- When a table node is encountered check that the given description
-- matches the actual table information in the database.
transformE (TableE (TableDB n ks) ty) = do
                                    fv <- freshVar
                                    let tTy@(FList (FRec ts)) = flatFTy ty
                                    let varB = Var ([] :=> FRec ts) $ prefixVar fv
                                    tableDescr <- tableInfo n
                                    let tyDescr = case length tableDescr == length ts of
                                                    True -> zip tableDescr ts
                                                    False -> error $ "Inferred typed: " ++ show tTy ++ " \n doesn't match type of table: \"" 
                                                                        ++ n ++ "\" in the database. The table has the shape: " ++ (show $ map fst tableDescr) ++ ". " ++ show ty 
                                    let cols = [Column cn t | ((cn, f), (RLabel i, t)) <- tyDescr, legalType n cn i t f]
                                    let keyCols = (nub $ concat ks) L.\\ (map fst tableDescr)
                                    let keys = if (keyCols == [])
                                                    then if (ks /= []) then map Key ks else [Key $ map (\(Column n' _) -> n') cols]
                                                    else error $ "The following columns were used as key but not a column of table " ++ n ++ " : " ++ show keyCols
                                    let table' = Table ([] :=> tTy) n cols keys
                                    let pattern = [prefixVar fv]
                                    let nameType = map (\(Column name t) -> (name, t)) cols 
                                    let body = foldr (\(nr, t) b -> 
                                                    let (_ :=> bt) = typeOf b
                                                     in Rec ([] :=> FRec [(RLabel "1", t), (RLabel "2", bt)]) [RecElem ([] :=> t) "1" (F.Elem ([] :=> t) varB nr), RecElem ([] :=> bt) "2" b])
                                                  ((\(nr,t) -> F.Elem ([] :=> t) varB nr) $ last nameType)
                                                  (init nameType)
                                    let ([] :=> rt) = typeOf body
                                    let lambda = ParAbstr ([] :=> FRec ts .-> rt) pattern body
                                    let expr = App ([] :=> FList rt) (App ([] :=> (FList $ FRec ts) .-> FList rt) 
                                                                    (Var ([] :=> (FRec ts .-> rt) .-> (FList $ FRec ts) .-> FList rt) "map") 
                                                                    lambda)
                                                                   (ParExpr (typeOf table') table') 
                                    return expr
    where
        legalType :: String -> String -> String -> FType -> (FType -> Bool) -> Bool
        legalType tn cn nr t f = case f t of
                                True -> True
                                False -> error $ "The type: " ++ show t ++ "\nis not compatible with the type of column nr: " ++ nr
                                                    ++ " namely: " ++ cn ++ "\n in table " ++ tn ++ "."
transformE (LamE _ _) = $impossible
-}
{-


-- | Transform a function argument
transformArg :: (IConnection conn) => Exp a -> N conn Param                                 
transformArg ((LamE f) :: Exp t) = do
                                  let ty = reify (undefined :: t)
                                  n <- freshVar
                                  let fty = transformTy ty
                                  let e1 = f $ VarE $ fromIntegral n 
                                  case e1 of
                                    l@(LamE _) -> do
                                               (ParAbstr _ vs e') <- transformArg l
                                               return $ ParAbstr ([] :=> fty) ((prefixVar n):vs) e'
                                    _           -> ParAbstr ([] :=> fty) [prefixVar n] <$> transformE e1
transformArg e = (\e' -> ParExpr (typeOf e') e') <$> transformE e 
-}

transformL1Arg :: forall conn a b. (IConnection conn, QA a, QA b) => Exp (a -> b) -> N conn Param
transformL1Arg ((Lam1E f)::Exp (a -> b)) = do 
                                          let ty = reify (undefined :: (a -> b))
                                          n <- freshVar
                                          let fty = transformTy ty
                                          let e1 = f $ VarE $ fromIntegral n 
                                          ParAbstr ([] :=> fty) [prefixVar n] <$> transformE e1

transformArg :: (IConnection conn, QA a) => Exp a -> N conn Param
transformArg e = (\e' -> ParExpr (typeOf e') e') <$> transformE e
 
-- | Construct a flat-FerryCore type out of a DSH type
-- A flat type consists out of two tuples, a record is translated as:
-- {r1 :: t1, r2 :: t2, r3 :: t3, r4 :: t4} (t1, (t2, (t3, t4)))
flatFTy :: Type a -> FType
flatFTy (ListT t) = FList $ FRec $ flatFTy' 1 t
 where
     flatFTy' :: Int -> Type a -> [(RLabel, FType)]
     flatFTy' i (PairT t1 t2) = (RLabel $ show i, transformTy t1) : (flatFTy' (i + 1) t2)
     flatFTy' i ty              = [(RLabel $ show i, transformTy ty)]
flatFTy _         = $impossible

-- Determine the size of a flat type
sizeOfTy :: Type a -> Int
sizeOfTy (PairT _ t2) = 1 + sizeOfTy t2
sizeOfTy _              = 1 

-- | Transform an arbitrary DSH-type into a ferry core type 
transformTy :: Type a -> FType
transformTy UnitT = int
transformTy BoolT = bool
transformTy CharT = string
transformTy TextT = string
transformTy IntegerT = int
transformTy DoubleT = float
transformTy (PairT t1 t2) = FRec [(RLabel "1", transformTy t1), (RLabel "2", transformTy t2)]
transformTy (ListT t1) = FList $ transformTy t1
transformTy (ArrowT t1 t2) = (transformTy t1) .-> (transformTy t2)

{-
-- | Translate the DSH operator to Ferry Core operators
transformOp :: Fun2 -> Op
transformOp Add = Op "+"
transformOp Sub = Op "-"
transformOp Mul = Op "*"
transformOp Div = Op "/"
transformOp Equ = Op "=="
transformOp Lt = Op "<"
transformOp Lte = Op "<="
transformOp Gte = Op ">="
transformOp Gt = Op ">"
transformOp Conj = Op "&&"
transformOp Disj = Op "||"
transformOp _ = $impossible
-}

-- | Transform a DSH-primitive-function (f) with an instantiated typed into a FerryCore
-- expression
transformF :: (Show f) => f -> FType -> CoreExpr
transformF f t = Var ([] :=> t) $ (\txt -> case txt of
                                            (x:xs) -> toLower x : xs
                                            _      -> $impossible) $ show f

{-
-- | Retrieve all DB-table names from a DSH program
getTableNames :: Exp a -> [String]
getTableNames e = let tables = map (\t -> case t of
                                        (TableE (TableDB n _)) -> n
                                        _                        -> $impossible) $ listify isTable e
                   in nub tables
    where 
        isTable :: Exp a -> Bool
        isTable (TableE (TableDB _ _)) = True
        isTable _                        = False
-}
-- | Retrieve through the given database connection information on the table (columns with their types)
-- which name is given as the second argument.        
getTableInfo :: IConnection conn => conn -> String -> IO [(String, (FType -> Bool))]
getTableInfo c n = do
                    info <- describeTable c n
                    return $ toTableDescr info
                    
        where
          toTableDescr :: [(String, SqlColDesc)] -> [(String, (FType -> Bool))]
          toTableDescr = L.sortBy (\(n1, _) (n2, _) -> compare n1 n2) . map (\(name, props) -> (name, compatibleType (colType props)))
          compatibleType :: SqlTypeId -> FType -> Bool
          compatibleType dbT hsT = case hsT of
                                        FUnit -> True
                                        FBool -> L.elem dbT [SqlSmallIntT, SqlIntegerT, SqlBitT]
                                        FString -> L.elem dbT [SqlCharT, SqlWCharT, SqlVarCharT]
                                        FInt -> L.elem dbT [SqlSmallIntT, SqlIntegerT, SqlTinyIntT, SqlBigIntT, SqlNumericT]
                                        FFloat -> L.elem dbT [SqlDecimalT, SqlRealT, SqlFloatT, SqlDoubleT]
                                        t       -> error $ "You can't store this kind of data in a table... " ++ show t ++ " " ++ show n
