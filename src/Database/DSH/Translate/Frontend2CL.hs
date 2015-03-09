{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Translate DSH frontend expressions (implicitly typed through
-- GADT) into explicitly typed DSH backend expressions.
module Database.DSH.Translate.Frontend2CL
    ( toComprehensions
    , TableInfo
    ) where

import           Database.DSH.Common.Impossible

import qualified Database.DSH.CL.Lang            as CL
import qualified Database.DSH.CL.Primitives      as CP
import qualified Database.DSH.Common.Lang        as L
import qualified Database.DSH.Common.Type        as T

import           Data.Text                       (unpack)
import           Database.DSH.Frontend.Builtins
import           Database.DSH.Frontend.TupleTypes
import           Database.DSH.Frontend.Internals
import           Database.DSH.Backend

import qualified Data.Map                        as M

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State

import           Text.Printf

import           GHC.Exts                        (sortWith)

-- In the state, we store a counter for fresh variable names, the
-- cache for table information and the backend connection 'c'.
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
toComprehensions q = runCompile (translate q)

-- | Execute the transformation computation. During compilation table
-- information can be retrieved from the database, therefore the result
-- is wrapped in the IO Monad.
runCompile :: Compile a -> a
runCompile ma = evalState ma 1

lamBody :: forall a b.(Reify a, Reify b)
        => (Exp a -> Exp b)
        -> Compile (L.Ident, Exp b)
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
translate (DecimalE d) = return $ CP.decimal d
translate (DayE d) = return $ CP.day d
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
translate (TableE (TableDB tableName colNames hints)) = do
    -- Reify the type of the table expression
    let ty = reify (undefined :: a)
    let colNames' = map L.ColName colNames

    return $ CP.table (translateType ty) tableName colNames' (compileHints hints)

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
translateType :: Type a -> T.Type
translateType UnitT          = T.unitT
translateType BoolT          = T.boolT
translateType CharT          = T.stringT
translateType IntegerT       = T.intT
translateType DoubleT        = T.doubleT
translateType DecimalT       = T.DecimalT
translateType TextT          = T.stringT
translateType DayT           = T.DateT
translateType (ListT t)      = T.listT (translateType t)
translateType (TupleT tupTy) = let translateTupleType = $(mkTranslateType 16)
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
       -- sortWith (\x -> f x) xs => sort [ (x, f x) | x <- xs ]
       SortWith     ->
           case args of
               TupleConstE (Tuple2E (LamE lam) xs) -> do
                   xs'                  <- translate xs
                   -- Get a FOAS representation of the lambda
                   (boundName, sortExp) <- lamBody lam
                   sortExp'             <- translate sortExp

                   let boundVar = CL.Var (T.elemT $ T.typeOf xs') boundName

                   return $ CP.sort $ CP.singleGenComp (CP.pair boundVar sortExp') boundName xs'
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
                   return $ CL.Comp xt (CL.Var xt boundVar) quals
               _ -> $impossible

       -- Map to a first-order combinator 'group'
       -- groupWithKey (\x -> f x) xs => group [ (x, f x) | x <- xs ]
       GroupWithKey ->
           case args of
               TupleConstE (Tuple2E (LamE lam) xs) -> do
                   xs'                   <- translate xs
                   (boundName, groupExp) <- lamBody lam
                   groupExp'             <- translate groupExp

                   let boundVar = CL.Var (T.elemT $ T.typeOf xs') boundName

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
       DiffDays     -> translateApp2 CP.addDays args

       -- Builtin functions with arity one
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
       Head             -> translateApp1 CP.head args
       Tail             -> translateApp1 CP.tail args
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
       Init             -> translateApp1 CP.init args
       Last             -> translateApp1 CP.last args
       Nub              -> translateApp1 CP.nub args
       Guard            -> translateApp1 CP.guard args
       Transpose        -> translateApp1 CP.transpose args
       Reshape n        -> translateApp1 (CP.reshape n) args
       TupElem te       -> let compileTupElem = $(mkTupElemCompile 16)
                           in compileTupElem te args
