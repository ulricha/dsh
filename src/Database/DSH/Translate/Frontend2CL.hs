{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Translate DSH frontend expressions (implicitly typed through
-- GADT) into explicitly typed DSH backend expressions.
module Database.DSH.Translate.Frontend2CL (toComprehensions) where

import           Database.DSH.Impossible

import qualified Database.DSH.CL.Lang            as CL
import qualified Database.DSH.CL.Primitives      as CP
import qualified Database.DSH.Common.Lang        as L
import qualified Database.DSH.Common.Type        as T

import           Data.Text                       (unpack)
import           Database.DSH.Frontend.Funs
import           Database.DSH.Frontend.TupleTypes
import           Database.DSH.Frontend.Internals

import qualified Data.Map                        as M

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State

import           Text.Printf

import           GHC.Exts                        (sortWith)

-- | For each column, we need the name of the column, a string
-- description of the type for error messsages and a function to check
-- a DSH base type for compability with the column.
type TableInfo = [(String, String, (T.Type -> Bool))]

type TableInfoCache = M.Map String TableInfo

type QueryTableInfo = String -> IO TableInfo

-- In the state, we store a counter for fresh variable names, the
-- cache for table information and the backend-specific IO function
-- that retrieves not-yet-cached table information.
type CompileState = (Integer, TableInfoCache, QueryTableInfo)

-- | The Compile monad provides fresh variable names, allows to
-- retrieve information about tables from the database backend and
-- caches table information.
type Compile = StateT  CompileState IO

-- | Lookup information that describes a table. If the information is
-- not present in the state then the connection is used to retrieve
-- the table information from the Database.
tableInfo :: String -> Compile TableInfo
tableInfo tableName = do
    (i, env, f) <- get
    case M.lookup tableName env of
        Nothing -> do
            inf <- getTableInfoFun tableName
            put (i, M.insert tableName inf env, f)
            return inf
        Just v -> return v

-- | Provide a fresh identifier name during compilation
freshVar :: Compile Integer
freshVar = do
    (i, m, f) <- get
    put (i + 1, m, f)
    return i

prefixVar :: Integer -> String
prefixVar i = "v" ++ show i

getTableInfoFun :: String -> Compile TableInfo
getTableInfoFun tableName = do
    (_, _, queryTableInfo) <- get
    lift $ queryTableInfo tableName

-- | Translate a DSH frontend expression into the internal
-- comprehension-based language. 'queryTableInfo' abstracts asking a
-- database for information about tables, which might be performed
-- using one of the existing backends (X100, SQL).
toComprehensions :: QueryTableInfo -> Exp a -> IO CL.Expr
toComprehensions queryTableInfo e = runCompile queryTableInfo $ translate e

-- | Execute the transformation computation. During compilation table
-- information can be retrieved from the database, therefore the result
-- is wrapped in the IO Monad.
runCompile :: QueryTableInfo -> Compile a -> IO a
runCompile f = liftM fst . flip runStateT (1, M.empty, f)

lamBody :: forall a b.(Reify a, Reify b) => (Exp a -> Exp b) -> Compile (L.Ident, Exp b)
lamBody f = do
    v <- freshVar
    return (prefixVar v, f (VarE v :: Exp a))

-- | Translate a frontend HOAS AST to a FOAS AST in Comprehension
-- Language (CL).
translate :: forall a. Exp a -> Compile CL.Expr
translate (TupleConstE tc) = let translateTupleConst = $(mkTranslateTupleTerm 16)
                             in translateTupleConst tc
translate UnitE = return $ CP.unit
translate (BoolE b) = return $ CP.bool b
translate (CharE c) = return $ CP.string [c]
translate (IntegerE i) = return $ CP.int (fromInteger i)
translate (DoubleE d) = return $ CP.double d
translate (TextE t) = return $ CP.string (unpack t)
translate (VarE i) = do
    let ty = reify (undefined :: a)
    return $ CP.var (translateType ty) (prefixVar i)
translate (ListE es) = do
    let ty = reify (undefined :: a)
    CP.list (translateType ty) <$> mapM translate es
-- We expect the query language to be first order. Lambdas must only
-- occur as an argument to higher-order built-in combinators (map,
-- concatMap, sortWith, ...). If lambdas occur in other places that
-- have not been eliminated by inlining in the frontend, additional
-- normalization rules or defunctionalization should be employed.
translate (LamE _) = $impossible
translate (TableE (TableDB tableName hints)) = do
    -- Reify the type of the table expression
    let ty = reify (undefined :: a)

    -- Extract the column types from the frontend type
    let ts = T.tupleElemTypes $ T.elemT $ translateType ty

    -- Fetch the actual type of the table from the database
    -- backend. Since we can't refer to columns by name from the
    -- Haskell side, we sort the columns by name to get a canonical
    -- order.
    tableDescr <- sortWith (\(n, _, _) -> n) <$> tableInfo tableName

    let tableTypeError = printf "DSH type and type of table %s are incompatible:\nDSH: %s\nDatabase: %s"
                                tableName
                                (show ts)
                                (show $ map (\(n, t, _) -> (n, t)) tableDescr)

    -- The DSH record/tuple type must match the number of columns in
    -- the database table
    if length tableDescr == length ts
        then return ()
        else error tableTypeError

    let matchTypes :: (String, String, T.Type -> Bool) -> T.Type -> (L.ColName, T.Type)
        matchTypes (colName, _, typesCompatible) dshType =
            if typesCompatible dshType
            then (L.ColName colName, dshType)
            else error tableTypeError

    let cols = zipWith matchTypes tableDescr ts

    return $ CP.table (translateType ty) tableName cols (compileHints hints)

translate (AppE f args) = translateApp f args

compileHints :: TableHints -> L.TableHints
compileHints hints = L.TableHints { L.keysHint = keys $ keysHint hints
                                  , L.nonEmptyHint = ne $ nonEmptyHint hints
                                  }
  where
    keys :: [Key] -> [L.Key]
    keys ks = [ L.Key [ L.ColName c | c <- k ] | Key k <- ks ]

    ne :: Emptiness -> L.Emptiness
    ne NonEmpty      = L.NonEmpty
    ne PossiblyEmpty = L.PossiblyEmpty


translateApp3 :: (CL.Expr -> CL.Expr -> CL.Expr -> CL.Expr) -> Exp (a, b, c) -> Compile CL.Expr
translateApp3 f (TupleConstE (Tuple3E e1 e2 e3)) = f <$> translate e1 <*> translate e2 <*> translate e3
translateApp3 _ _ = $impossible

translateApp2 :: (CL.Expr -> CL.Expr -> CL.Expr) -> Exp (a, b) -> Compile CL.Expr
translateApp2 f (TupleConstE (Tuple2E e1 e2)) = f <$> translate e1 <*> translate e2
translateApp2 _ _ = $impossible

translateApp1 :: (CL.Expr -> CL.Expr) -> Exp a -> Compile CL.Expr
translateApp1 f e = f <$> translate e

-- | Translate DSH frontend types into backend types.
translateType :: Type a -> T.Type
translateType UnitT          = T.unitT
translateType BoolT          = T.boolT
translateType CharT          = T.stringT
translateType IntegerT       = T.intT
translateType DoubleT        = T.doubleT
translateType TextT          = T.stringT
translateType (ListT t)      = T.listT (translateType t)
translateType (ArrowT t1 t2) = (translateType t1) T..-> (translateType t2)
translateType (TupleT tupTy) = let translateTupleType = $(mkTranslateType 16)
                               in translateTupleType tupTy

-- | From the type of a table (a list of base records represented as
-- right-deep nested tuples) extract the types of the individual
-- fields.

translateApp :: Fun a b -> Exp a -> Compile CL.Expr
translateApp f args =
    case f of
       -- Builtin functions with arity three
       Cond -> translateApp3 CP.cond args

       -- Builtin functions with arity two
       Add          -> translateApp2 CP.add args
       Mul          -> translateApp2 CP.mul args
       Sub          -> translateApp2 CP.sub args
       Div          -> translateApp2 CP.div args
       Mod          -> translateApp2 CP.mod args
       Index        -> translateApp2 CP.index args
       Cons         -> translateApp2 CP.cons args

       -- Map to a comprehension
       Map          -> 
           case args of
               TupleConstE (Tuple2E (LamE lam) xs) -> do
                   xs'                 <- translate xs
                   (boundVar, bodyExp) <- lamBody lam
                   bodyExp'            <- translate bodyExp
                   return $ CP.singleGenComp bodyExp' boundVar xs'
               _ -> $impossible

       -- Map to a comprehension and concat
       ConcatMap    -> 
           case args of
               TupleConstE (Tuple2E (LamE lam) xs) -> do
                   xs'                 <- translate xs
                   (boundVar, bodyExp) <- lamBody lam
                   bodyExp'            <- translate bodyExp
                   return $ CP.concat $ CP.singleGenComp bodyExp' boundVar xs'
               _ -> $impossible
               
       -- Map to a first-order combinator 'sort'
       SortWith     -> 
           case args of
               TupleConstE (Tuple2E (LamE lam) xs) -> do
                   xs'                 <- translate xs
                   (boundVar, bodyExp) <- lamBody lam
                   bodyExp'            <- translate bodyExp
                   genName             <- prefixVar <$> freshVar

                   let genVar = CL.Var (T.typeOf xs') genName
                       ss     = CP.singleGenComp bodyExp' boundVar genVar 
                   return $ CP.let_ genName xs' (CP.sort genVar ss)
               _ -> $impossible

       -- Map to a comprehension with a guard
       Filter       -> 
           case args of
               TupleConstE (Tuple2E (LamE lam) xs) -> do
                   xs'                 <- translate xs
                   (boundVar, bodyExp) <- lamBody lam
                   bodyExp'            <- translate bodyExp
                   let xt    = T.typeOf xs'
                       quals = CL.BindQ boundVar xs' CL.:* (CL.S $ CL.GuardQ bodyExp')
                   return $ CL.Comp (T.listT xt) (CL.Var xt boundVar) quals
               _ -> $impossible

       -- Map to a first-order combinator 'group'
       GroupWithKey ->
           case args of
               TupleConstE (Tuple2E (LamE lam) xs) -> do
                   xs'                 <- translate xs
                   (boundVar, bodyExp) <- lamBody lam
                   bodyExp'            <- translate bodyExp
                   genName             <- prefixVar <$> freshVar

                   let genVar = CL.Var (T.typeOf xs') genName
                       ss     = CP.singleGenComp bodyExp' boundVar genVar 
                   return $ CP.let_ genName xs' (CP.group genVar ss)
               _ -> $impossible

       Append       -> translateApp2 CP.append args
       Zip          -> translateApp2 CP.zip args
       Equ          -> translateApp2 CP.eq args
       NEq          -> translateApp2 CP.neq args
       Conj         -> translateApp2 CP.conj args
       Disj         -> translateApp2 CP.disj args
       Lt           -> translateApp2 CP.lt args
       Lte          -> translateApp2 CP.lte args
       Gte          -> translateApp2 CP.gte args
       Gt           -> translateApp2 CP.gt args
       Like         -> translateApp2 CP.like args

       -- Builtin functions with arity one
       SubString f t   -> translateApp1 (CP.substring f t) args
       IntegerToDouble -> translateApp1 CP.castDouble args
       Not             -> translateApp1 CP.not args
       Sin             -> translateApp1 CP.sin args
       Cos             -> translateApp1 CP.cos args
       Tan             -> translateApp1 CP.tan args
       ASin            -> translateApp1 CP.asin args
       ACos            -> translateApp1 CP.acos args
       ATan            -> translateApp1 CP.atan args
       Sqrt            -> translateApp1 CP.sqrt args
       Log             -> translateApp1 CP.log args
       Exp             -> translateApp1 CP.exp args
       Fst             -> translateApp1 CP.fst args
       Snd             -> translateApp1 CP.snd args
       Head            -> translateApp1 CP.head args
       Tail            -> translateApp1 CP.tail args
       Minimum         -> translateApp1 CP.minimum args
       Maximum         -> translateApp1 CP.maximum args
       Concat          -> translateApp1 CP.concat args
       Sum             -> translateApp1 CP.sum args
       Avg             -> translateApp1 CP.avg args
       And             -> translateApp1 CP.and args
       Or              -> translateApp1 CP.or args
       Reverse         -> translateApp1 CP.reverse args
       Number          -> translateApp1 CP.number args
       Length          -> translateApp1 CP.length args
       Null            -> translateApp1 CP.null args
       Init            -> translateApp1 CP.init args
       Last            -> translateApp1 CP.last args
       Nub             -> translateApp1 CP.nub args
       Guard           -> translateApp1 CP.guard args
       Transpose       -> translateApp1 CP.transpose args
       Reshape n       -> translateApp1 (CP.reshape n) args
       TupElem te      -> let compileTupElem = $(mkTupElemCompile 16)
                          in compileTupElem te args
