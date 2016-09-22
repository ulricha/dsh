{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Translate DSH frontend expressions (implicitly typed through
-- GADT) into explicitly typed DSH backend expressions.
module Database.DSH.Translate.Frontend2CL
    ( toComprehensions
    ) where

import           Control.Monad.State
import           Data.List.NonEmpty               (NonEmpty((:|)))
import qualified Data.List.NonEmpty               as N
import qualified Data.Text                        as T
import           Text.Printf

import           GHC.Exts

import qualified Database.DSH.CL.Lang             as CL
import qualified Database.DSH.CL.Primitives       as CP
import           Database.DSH.Common.Impossible
import qualified Database.DSH.Common.Lang         as L
import qualified Database.DSH.Common.Type         as Ty
import           Database.DSH.Frontend.Builtins
import           Database.DSH.Frontend.Internals
import           Database.DSH.Frontend.TupleTypes

-- In the state, we store a counter for fresh variable names.
type CompileState = Integer

-- | The Compile monad provides fresh variable names.
type Compile = State CompileState

-- | Provide a fresh identifier name during compilation
freshVar :: Compile Integer
freshVar = do
    i <- get
    put $ i + 1
    return i

prefixVar :: Integer -> String
prefixVar i = "v" ++ show i

-- | Translate a DSH frontend expression into the internal
-- comprehension-based language.
toComprehensions :: Exp a -> CL.Expr
toComprehensions q =
    -- The query compiler supports only queries that return a list. If the
    -- frontend query returns a scalar value, we wrap the query in a
    -- comprehension with a singleton unit generator.
    --
    -- Note that this comprehension is the outermost binder. Therefore, we can
    -- choose the generator name freely without taking care to shadow other
    -- names.
    case Ty.typeOf cl of
        Ty.ListT _ -> cl
        _          -> CP.singleGenComp cl "wrap" (uncurry CL.Lit L.sngUnitList)
  where
    cl = runCompile (translate q)

-- | Execute the transformation computation. During compilation table
-- information can be retrieved from the database, therefore the result
-- is wrapped in the IO Monad.
runCompile :: Compile a -> a
runCompile ma = evalState ma 1

lamBody :: forall a b.Reify a => (Exp a -> Exp b) -> Compile (L.Ident, Exp b)
lamBody f = do
    v <- freshVar
    return (prefixVar v, f (VarE v :: Exp a))

-- | Translate a frontend HOAS AST to a FOAS AST in Comprehension
-- Language (CL).
translate :: forall a. Exp a -> Compile CL.Expr
translate (TupleConstE tc) = let translateTupleConst :: TupleConst a -> Compile CL.Expr
                                 translateTupleConst = $(mkTranslateTupleTerm 16)
                             in translateTupleConst tc
translate UnitE = return CP.unit
translate (BoolE b) = return $ CP.bool b
translate (CharE c) = return $ CP.string $ T.singleton c
translate (IntegerE i) = return $ CP.int (fromInteger i)
translate (DoubleE d) = return $ CP.double d
translate (TextE t) = return $ CP.string t
translate (DecimalE d) = return $ CP.decimal $ fromRational $ toRational d
translate (ScientificE d) = return $ CP.decimal d
translate (DayE d) = return $ CP.day $ L.Date d
translate (VarE i) = do
    let ty = reify (undefined :: a)
    return $ CP.var (translateType ty) (prefixVar i)
translate (ListE es) = do
    let ty = reify (undefined :: a)
    CP.list (translateType ty) <$> mapM translate (toList es)
-- We expect the query language to be first order. Lambdas must only
-- occur as an argument to higher-order built-in combinators (map,
-- concatMap, sortWith, ...). If lambdas occur in other places that
-- have not been eliminated by inlining in the frontend, additional
-- normalization rules or defunctionalization should be employed.
translate (LamE _) = $impossible
translate (TableE (TableDB tableName colNames hints)) = do
    -- Reify the type of the table expression
    let ty = reify (undefined :: a)
    let colNames' = fmap L.ColName colNames
    let bty = translateType ty

    return $ CP.table bty tableName (schema tableName colNames' bty hints)

translate (AppE f args) = translateApp f args

schema :: String -> N.NonEmpty L.ColName -> Ty.Type -> TableHints -> L.BaseTableSchema
schema tableName cols ty hints =
    L.BaseTableSchema { L.tableCols     = colTys
                      , L.tableKeys     = keys (keysHint hints)
                      , L.tableNonEmpty = ne $ nonEmptyHint hints
                      }
  where
    colTys :: NonEmpty L.ColumnInfo
    colTys = case Ty.elemT ty of
        Ty.TupleT ts@(_:_) | length ts == N.length cols ->
            case mapM Ty.scalarType ts of
                Just (st : sts) -> N.zip cols (st :| sts)
                _               -> error errMsgScalar
        (Ty.ScalarT st)      | N.length cols == 1       ->
            N.zip cols (st :| [])
        _                                              ->
            error errMsgLen

    errMsgLen = printf "Type for table %s does not match column specification"
                       tableName

    errMsgScalar = printf "Non-scalar types in table %s" tableName

    keys :: N.NonEmpty Key -> N.NonEmpty L.Key
    keys = fmap (\(Key k) -> L.Key $ fmap L.ColName k)

    ne :: Emptiness -> L.Emptiness
    ne NonEmpty      = L.NonEmpty
    ne PossiblyEmpty = L.PossiblyEmpty


translateApp3 :: (CL.Expr -> CL.Expr -> CL.Expr -> CL.Expr)
              -> Exp (a, b, c)
              -> Compile CL.Expr
translateApp3 f (TupleConstE (Tuple3E e1 e2 e3)) =
    f <$> translate e1 <*> translate e2 <*> translate e3
translateApp3 _ _ = $impossible

translateApp2 :: (CL.Expr -> CL.Expr -> CL.Expr)
              -> Exp (a, b)
              -> Compile CL.Expr
translateApp2 f (TupleConstE (Tuple2E e1 e2)) =
    f <$> translate e1 <*> translate e2
translateApp2 _ _ = $impossible

translateApp1 :: (CL.Expr -> CL.Expr) -> Exp a -> Compile CL.Expr
translateApp1 f e = f <$> translate e

-- | Translate DSH frontend types into backend types.
translateType :: Type a -> Ty.Type
translateType UnitT          = Ty.PUnitT
translateType BoolT          = Ty.PBoolT
translateType CharT          = Ty.PStringT
translateType IntegerT       = Ty.PIntT
translateType DoubleT        = Ty.PDoubleT
translateType DecimalT       = Ty.PDecimalT
translateType ScientificT    = Ty.PDecimalT
translateType TextT          = Ty.PStringT
translateType DayT           = Ty.PDateT
translateType (ListT t)      = Ty.ListT (translateType t)
translateType (TupleT tupTy) = let translateTupleType :: TupleType a -> Ty.Type
                                   translateTupleType = $(mkTranslateType 16)
                               in translateTupleType tupTy
translateType (ArrowT _ _)   = $impossible

translateApp :: Fun a b -> Exp a -> Compile CL.Expr
translateApp f args =
    case f of
       -- Builtin functions with arity three
       Cond         -> translateApp3 CP.cond args

       -- Builtin functions with arity two
       Add          -> translateApp2 CP.add args
       Mul          -> translateApp2 CP.mul args
       Sub          -> translateApp2 CP.sub args
       Div          -> translateApp2 CP.div args
       Mod          -> translateApp2 CP.mod args
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
       -- sortWith (\x -> f x) xs => sort [ (x, f x) | x <- xs ]
       SortWith     ->
           case args of
               TupleConstE (Tuple2E (LamE lam) xs) -> do
                   xs'                  <- translate xs
                   -- Get a FOAS representation of the lambda
                   (boundName, sortExp) <- lamBody lam
                   sortExp'             <- translate sortExp

                   let boundVar = CL.Var (Ty.elemT $ Ty.typeOf xs') boundName

                   return $ CP.sort $ CP.singleGenComp (CP.pair boundVar sortExp') boundName xs'
               _ -> $impossible

       -- Map to a comprehension with a guard
       Filter       ->
           case args of
               TupleConstE (Tuple2E (LamE lam) xs) -> do
                   xs'                 <- translate xs
                   (boundVar, bodyExp) <- lamBody lam
                   bodyExp'            <- translate bodyExp
                   let xst   = Ty.typeOf xs'
                       quals = CL.BindQ boundVar xs' CL.:* (CL.S $ CL.GuardQ bodyExp')
                   return $ CL.Comp xst (CL.Var (Ty.elemT xst) boundVar) quals
               _ -> $impossible

       -- Map to a first-order combinator 'group'
       -- groupWithKey (\x -> f x) xs => group [ (x, f x) | x <- xs ]
       GroupWithKey ->
           case args of
               TupleConstE (Tuple2E (LamE lam) xs) -> do
                   xs'                   <- translate xs
                   (boundName, groupExp) <- lamBody lam
                   groupExp'             <- translate groupExp

                   let boundVar = CL.Var (Ty.elemT $ Ty.typeOf xs') boundName

                   return $ CP.group $ CP.singleGenComp (CP.pair boundVar groupExp') boundName xs'

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
       AddDays      -> translateApp2 CP.addDays args
       SubDays      -> translateApp2 CP.subDays args
       DiffDays     -> translateApp2 CP.diffDays args

       -- Builtin functions with arity one
       Only             -> translateApp1 CP.only args
       SubString s e    -> translateApp1 (CP.substring s e) args
       IntegerToDouble  -> translateApp1 CP.castDouble args
       IntegerToDecimal -> translateApp1 CP.castDecimal args
       Not              -> translateApp1 CP.not args
       Sin              -> translateApp1 CP.sin args
       Cos              -> translateApp1 CP.cos args
       Tan              -> translateApp1 CP.tan args
       ASin             -> translateApp1 CP.asin args
       ACos             -> translateApp1 CP.acos args
       ATan             -> translateApp1 CP.atan args
       Sqrt             -> translateApp1 CP.sqrt args
       Log              -> translateApp1 CP.log args
       Exp              -> translateApp1 CP.exp args
       DayDay           -> translateApp1 CP.dateDay args
       DayMonth         -> translateApp1 CP.dateMonth args
       DayYear          -> translateApp1 CP.dateYear args
       Fst              -> translateApp1 CP.fst args
       Snd              -> translateApp1 CP.snd args
       Minimum          -> translateApp1 CP.minimum args
       Maximum          -> translateApp1 CP.maximum args
       Concat           -> translateApp1 CP.concat args
       Sum              -> translateApp1 CP.sum args
       Avg              -> translateApp1 CP.avg args
       And              -> translateApp1 CP.and args
       Or               -> translateApp1 CP.or args
       Reverse          -> translateApp1 CP.reverse args
       Number           -> translateApp1 CP.number args
       Length           -> translateApp1 CP.length args
       Null             -> translateApp1 CP.null args
       Nub              -> translateApp1 CP.nub args
       Guard            -> translateApp1 CP.guard args
       TupElem te       -> do
           e' <- translate args
           let tupAcc = $(mkTupElemCompile 16) te
           return $ tupAcc e'
