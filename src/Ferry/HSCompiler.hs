{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, ScopedTypeVariables #-}

module Ferry.HSCompiler (fromQ) where

import Ferry.Data as D
import Ferry.Syntax as F
import Ferry.Compiler
import Ferry.Impossible
import Ferry.Compile as C

import qualified Data.Map as M
import Data.Char
import Database.HDBC

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

freshVar :: N conn Int
freshVar = do
             (c, i, env) <- get
             put (c, i + 1, env)
             return i
                
getConnection :: IConnection conn => N conn conn
getConnection = do
                 (c, _, _) <- get
                 return c

tableInfo :: IConnection conn => String -> N conn [(String, (FType -> Bool))]
tableInfo t = do
               (c, i, env) <- get
               case M.lookup t env of
                     Nothing -> do
                                 inf <- lift $ getTableInfo c t
                                 put (c, i, M.insert t inf env)
                                 return inf                                      
                     Just v -> return v
                    
prefixVar :: Int -> String
prefixVar = ((++) "__fv_") . show
     
runN :: IConnection conn => conn -> N conn a -> IO a
runN c  = liftM fst . flip runStateT (c, 1, M.empty)
            
-- * Convert DB queries into Haskell values
fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c a = evaluate c a >>= (return . fromNorm)

evaluate :: forall a. forall conn. (QA a, IConnection conn)
         => conn                -- ^ The HDBC connection
         -> Q a
         -> IO Norm
evaluate c q = do
                do
                  algPlan' <- doCompile c q
                  let algPlan = ((C.Algebra algPlan')::AlgebraXML a)
                  executePlan c algPlan
                   
doCompile :: IConnection conn => conn -> Q a -> IO String
doCompile c (Q a) = do 
                        core <- runN c $ transformE a
                        --putStrLn $ dotify' core
                        return $ typedCoreToAlgebra core


transformE :: IConnection conn => Exp -> N conn CoreExpr
transformE (UnitE _) = return $ Constant ([] :=> int) $ CInt 1
transformE (BoolE b _) = return $ Constant ([] :=> bool) $ CBool b
transformE (CharE c _) = return $ Constant ([] :=> string) $ CString [c] 
transformE (IntegerE i _) = return $ Constant ([] :=> int) $ CInt i
transformE (DoubleE d _) = return $ Constant ([] :=> float) $ CFloat d
transformE (TextE t _) = return $ Constant ([] :=> string) $ CString $ unpack t
transformE (TimeE _ _) = error "transformation of time values has not been implemented yet."
transformE (TupleE e1 e2 ty) = do
                                        c1 <- transformE e1
                                        c2 <- transformE e2
                                        return $ Rec ([] :=> transformTy ty) [RecElem (typeOf c1) "1" c1, RecElem (typeOf c2) "2" c2] 
transformE (ListE es ty) = let qt = ([] :=> transformTy ty) 
                                  in foldr (\h t -> F.Cons qt h t) (Nil qt) <$> mapM transformE es
transformE (AppE f a _) = transformE $ f a 
transformE (AppE1 f1 e1 ty) = do
                                      let tr = transformTy ty
                                      e1' <- transformArg e1
                                      let (_ :=> ta) = typeOf e1'
                                      return $ App ([] :=> tr) (transformF f1 (ta .-> tr)) e1'
-- transformE ((AppE2 GroupWith fn e) ::: ty) = transformE $ ListE [e] ::: ty
transformE (AppE2 GroupWith gfn e ty@(ListT (ListT tel))) = do
                                                let tr = transformTy ty
                                                fn' <- transformArg gfn
                                                let (_ :=> tfn@(FFn _ rt)) = typeOf fn'
                                                let gtr = list $ rec [(RLabel "1", rt), (RLabel "2", transformTy $ ListT tel)]
                                                e' <- transformArg e
                                                let (_ :=> te) = typeOf e'
                                                fv <- transformArg (LamE id $ ArrowT tel tel)
                                                snd' <- transformArg (LamE (\x -> AppE1 Snd x $ ArrowT (TupleT (transformTy' rt) (ListT tel)) (ListT tel)) $ ArrowT (TupleT (transformTy' rt) (ListT tel)) (ListT tel))
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
transformE (AppE2 D.Cons e1 e2 _) = do
                                            e1' <- transformE e1
                                            e2' <- transformE e2
                                            let (_ :=> t) = typeOf e1'
                                            return $ F.Cons ([] :=> list t) e1' e2'
transformE (AppE2 f2 e1 e2 ty) = do
                                        let tr = transformTy ty
                                        case elem f2 [Add, Mul, Div, Equ, Lt, Lte, Gte, Gt] of
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
transformE (TableE n ty) = do
                                    fv <- freshVar
                                    let tTy@(FList (FRec ts)) = flatFTy ty
                                    let varB = Var ([] :=> FRec ts) $ prefixVar fv
                                    tableDescr <- tableInfo n
                                    let tyDescr = case length tableDescr == length ts of
                                                    True -> zip tableDescr ts
                                                    False -> error $ "Inferred typed: " ++ show tTy ++ " \n doesn't match type of table: \"" 
                                                                        ++ n ++ "\" in the database. The table has the shape: " ++ (show $ map fst tableDescr) ++ ". " ++ show ty 
                                    let cols = [Column cn t | ((cn, f), (RLabel i, t)) <- tyDescr, legalType n cn i t f]
                                    let keys = [Key $ map (\(Column n' _) -> n') cols]
                                    let table' = Table ([] :=> tTy) n cols keys
                                    let pattern = PVar $ prefixVar fv
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

transformArg :: IConnection conn => Exp -> N conn Param                                 
transformArg (LamE f ty) = do
                                  n <- freshVar
                                  let (ArrowT t1 _) = ty
                                  let fty = transformTy ty
                                  let e1 = f $ VarE n t1
                                  ParAbstr ([] :=> fty) (PVar $ prefixVar n) <$> transformE e1
transformArg e = (\e' -> ParExpr (typeOf e') e') <$> transformE e 
                                  
parExpr :: CoreExpr -> Param
parExpr c = ParExpr (typeOf c) c

flatFTy :: Type -> FType
flatFTy (ListT t) = FList $ FRec $ flatFTy' 1 t
 where
     flatFTy' :: Int -> Type -> [(RLabel, FType)]
     flatFTy' i (TupleT t1 t2) = (RLabel $ show i, transformTy t1) : (flatFTy' (i + 1) t2)
     flatFTy' i ty              = [(RLabel $ show i, transformTy ty)]
flatFTy _         = $impossible

sizeOfTy :: Type -> Int
sizeOfTy (TupleT _ t2) = 1 + sizeOfTy t2
sizeOfTy _              = 1 

transformTy :: Type -> FType
transformTy UnitT = int
transformTy BoolT = bool
transformTy CharT = string
transformTy TextT = string
transformTy IntegerT = int
transformTy DoubleT = float
transformTy TimeT = error "transformation of time types has not been implemented yet."
transformTy (TupleT t1 t2) = FRec [(RLabel "1", transformTy t1), (RLabel "2", transformTy t2)]
transformTy (ListT t1) = FList $ transformTy t1
transformTy (ArrowT t1 t2) = (transformTy t1) .-> (transformTy t2)

transformTy' :: FType -> Type
transformTy' FUnit = UnitT
transformTy' FInt  = IntegerT
transformTy' FFloat = DoubleT
transformTy' FString = TextT
transformTy' FBool = BoolT
transformTy' (FList t) = ListT $ transformTy' t
transformTy' (FRec [(RLabel "1", t1), (RLabel "2", t2)]) = TupleT (transformTy' t1) (transformTy' t2)
transformTy' (FFn t1 t2) = ArrowT (transformTy' t1) (transformTy' t2)
transformTy' _ = $impossible

transformOp :: Fun2 -> Op
transformOp Add = Op "+"
transformOp Mul = Op "*"
transformOp Div = Op "/"
transformOp Equ = Op "=="
transformOp Lt = Op "<"
transformOp Lte = Op "<="
transformOp Gte = Op ">="
transformOp Gt = Op ">"
transformOp _ = $impossible

transformF :: (Show f) => f -> FType -> CoreExpr
transformF f t = Var ([] :=> t) $ (\(x:xs) -> toLower x : xs) $ show f

getTableNames :: Exp -> [String]
getTableNames e = let tables = map (\(TableE n _) -> n) $ listify isTable e
                   in nub tables
    where 
        isTable :: Exp -> Bool
        isTable (TableE _ _) = True
        isTable _            = False
        
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
