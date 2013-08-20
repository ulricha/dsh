{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}

module Database.DSH.CompileFlattening (toComprehensions) where

import           Database.DSH.Impossible

import qualified Database.DSH.CL.Lang as CL
import qualified Database.DSH.CL.Primitives as CP
import qualified Database.DSH.Common.Data.Type as T
import qualified Database.DSH.Common.Data.Val as V
import qualified Database.DSH.Common.Data.Op as O

import           Database.DSH.Internals as D
import           Data.Text (unpack)

import qualified Data.Map as M
import qualified Data.Set as S

import           Control.Monad
import           Control.Monad.State
import           Control.Applicative
       
import           Text.Printf
  
import           GHC.Exts(sortWith)

{-
N monad, version of the state monad that can provide fresh variable names.
-}
type N = StateT (Integer, M.Map String [(String, (T.Type -> Bool))], String -> IO [(String, T.Type -> Bool)]) IO

-- | Lookup information that describes a table. If the information is
-- not present in the state then the connection is used to retrieve the
-- table information from the Database.
tableInfo :: String -> N [(String, (T.Type -> Bool))]
tableInfo t = do
               (i, env, f) <- get
               case M.lookup t env of
                     Nothing -> do
                                 inf <- getTableInfoFun t
                                 put (i, M.insert t inf env, f)
                                 return inf
                     Just v -> return v

-- | Provide a fresh identifier name during compilation
freshVar :: N Integer
freshVar = do
             (i, m, f) <- get
             put (i + 1, m, f)
             return i

prefixVar :: Integer -> String
prefixVar i = "v" ++ show i

getTableInfoFun :: String -> N [(String, T.Type -> Bool)]
getTableInfoFun n = do
                   (_, _, f) <- get
                   lift $ f n

-- | Translate a DSH frontend expression into the internal comprehension-based
-- language
toComprehensions :: (String -> IO [(String, T.Type -> Bool)]) -> Exp a -> IO CL.Expr
toComprehensions f e = fmap resugar (runN f $ translate e)

-- | Execute the transformation computation. During
-- compilation table information can be retrieved from
-- the database, therefor the result is wrapped in the IO
-- Monad.
runN :: (String -> IO [(String, T.Type -> Bool)]) -> N a -> IO a
runN f = liftM fst . flip runStateT (1, M.empty, f)


translate ::  forall a. Exp a -> N CL.Expr
translate UnitE = return $ CP.unit
translate (BoolE b) = return $ CP.bool b
translate (CharE c) = return $ CP.string [c]
translate (IntegerE i) = return $ CP.int (fromInteger i)
translate (DoubleE d) = return $ CP.double d
translate (TextE t) = return $ CP.string (unpack t)
translate (PairE e1 e2) = CP.pair <$> translate e1 <*> translate e2
translate (VarE i) = do
                      let ty = reify (undefined :: a)
                      return $ CP.var (translateType ty) (prefixVar i)
translate (ListE es) = do
                        let ty = reify (undefined :: a)
                        CP.list (translateType ty) <$> mapM translate es
translate (e@(LamE _)) = case e of
                             (LamE f :: Exp (b -> c)) -> do
                                 v <- freshVar
                                 let ty = ArrowT (reify (undefined :: b)) (reify (undefined :: c))
                                 CP.lambda (translateType ty) (prefixVar v) <$> (translate $ f (VarE v :: Exp b))
                             _ -> $impossible
translate (TableE (TableDB n ks)) = do
                                        let ty = reify (undefined :: a)
                                        let ts = zip [1..] $ tableTypes ty
                                        tableDescr <- liftM (sortWith fst) $ tableInfo n
                                        let tyDescr = if length tableDescr == length ts
                                                        then zip tableDescr ts
                                                        else error $ printf "Inferred type\n%s doesn't match type of table %s\n%s\n%d %d" (show ts) n (show $ map fst tableDescr) (length tableDescr) (length ts)
                                        let cols = [(cn, t) | ((cn, f), (i, t)) <- tyDescr, legalType n cn i t f]
                                        let ks' = if ks == []
                                                    then [map fst tableDescr]
                                                    else ks
                                        return $ CP.table (translateType ty) n cols ks'
translate (TableE (TableCSV _)) = $impossible
translate (AppE f args) = compileApp f args

compileApp3 :: (CL.Expr -> CL.Expr -> CL.Expr -> CL.Expr) -> Exp (a, (b, c)) -> N CL.Expr
compileApp3 f (PairE e1 (PairE e2 e3)) = f <$> translate e1 <*> translate e2 <*> translate e3
compileApp3 _ _ = $impossible

compileApp2 :: (CL.Expr -> CL.Expr -> CL.Expr) -> Exp (a, b) -> N CL.Expr
compileApp2 f (PairE e1 e2) = f <$> translate e1 <*> translate e2
compileApp2 _ _ = $impossible

compileApp1 :: (CL.Expr -> CL.Expr) -> Exp a -> N CL.Expr
compileApp1 f e = f <$> translate e

compileApp :: Fun a b -> Exp a -> N CL.Expr
compileApp f args = case f of
                        Cond -> compileApp3 CP.cond args
                        Add       -> compileApp2 CP.add args
                        Mul       -> compileApp2 CP.mul args
                        Sub       -> compileApp2 CP.sub args
                        Div       -> compileApp2 CP.div args
                        Mod       -> compileApp2 CP.mod args
                        Index     -> compileApp2 CP.index args
                        SortWith  -> compileApp2 CP.sortWith args
                        Cons      -> compileApp2 CP.consOpt args
                        Take      -> compileApp2 CP.take args
                        Drop      -> compileApp2 CP.drop args
                        Map       -> compileApp2 CP.map args
                        ConcatMap -> compileApp2 CP.concatMap args
                        Append    -> compileApp2 CP.append args
                        Filter    -> compileApp2 CP.filter args
                        GroupWithKey -> compileApp2 CP.groupWithKey args
                        Zip       -> compileApp2 CP.zip args
                        DropWhile -> compileApp2 CP.dropWhile args
                        TakeWhile -> compileApp2 CP.takeWhile args
                        SplitAt   -> compileApp2 CP.splitAt args
                        Equ       -> compileApp2 CP.eq args
                        Conj      -> compileApp2 CP.conj args
                        Disj      -> compileApp2 CP.disj args
                        Lt        -> compileApp2 CP.lt args
                        Lte       -> compileApp2 CP.lte args
                        Gte       -> compileApp2 CP.gte args
                        Gt        -> compileApp2 CP.gt args
                        Max       -> compileApp2 CP.max args
                        Min       -> compileApp2 CP.min args
                        Like      -> compileApp2 CP.like args
                        Fst             -> compileApp1 CP.fst args
                        Snd             -> compileApp1 CP.snd args
                        Not             -> compileApp1 CP.not args
                        IntegerToDouble -> compileApp1 CP.integerToDouble args
                        Head            -> compileApp1 CP.head args
                        Tail            -> compileApp1 CP.tail args
                        Minimum         -> compileApp1 CP.minimum args
                        Maximum         -> compileApp1 CP.maximum args
                        Concat          -> compileApp1 CP.concat args
                        Sum             -> compileApp1 CP.sum args
                        Avg             -> compileApp1 CP.avg args
                        And             -> compileApp1 CP.and args
                        Or              -> compileApp1 CP.or args
                        Reverse         -> compileApp1 CP.reverse args
                        Number          -> compileApp1 CP.number args
                        Length          -> compileApp1 CP.length args
                        Null            -> compileApp1 CP.null args
                        Init            -> compileApp1 CP.init args
                        Last            -> compileApp1 CP.last args
                        Nub             -> compileApp1 CP.nub args
                        Guard           -> compileApp1 CP.guard args

legalType :: String -> String -> Int -> T.Type -> (T.Type -> Bool) -> Bool
legalType tn cn nr t f = case f t of
                            True -> True
                            False -> error $ "The type: " ++ show t ++ "\nis not compatible with the type of column nr: " ++ show nr
                                                ++ " namely: " ++ cn ++ "\n in table " ++ tn ++ "."

-- Restore the original comprehension form from the desugared concatMap form.
resugar :: CL.Expr -> CL.Expr
resugar expr = 
  case expr of 
    tab@(CL.Table _ _ _ _) -> tab
    CL.App t e1 e2 -> CL.App t (resugar e1) (resugar e2)

    -- This does not originate from a source comprehension, but is a
    -- normalization step to get as much as possible into comprehension form
    -- map (\x -> body) xs => [ body | x <- xs ]
    CL.AppE2 t (CL.Prim2 CL.Map _) (CL.Lam _ x body) xs ->
        let body' = resugar body
            xs'   = resugar xs
        in resugar $ CL.Comp t body' (CL.Quals [CL.BindQ x xs'])
  
    -- Another normalization step: Transform filter combinators to
    -- comprehensions
    -- filter (\x -> p) xs => [ x | x <- xs, p ]
    CL.AppE2 t (CL.Prim2 CL.Filter _) (CL.Lam (T.FunT xt _) x p) xs ->
        let xs' = resugar xs
            p'  = resugar p
        in resugar $ CL.Comp t (CL.Var xt x) (CL.Quals [CL.BindQ x xs', CL.GuardQ p'])
        
    CL.AppE1 t p1 e1 -> CL.AppE1 t p1 (resugar e1)
    
    -- (Try to) transform concatMaps into comprehensions
    cm@(CL.AppE2 t (CL.Prim2 CL.ConcatMap _) body xs) ->
      let xs' = resugar xs
      in 
    
      case resugar body of
        -- concatMap (\x -> [e]) xs
        -- => [ e | x < xs ]
        CL.Lam _ v (CL.BinOp _ O.Cons e (CL.Lit _ (V.ListV []))) ->
          resugar $ CL.Comp t e (CL.Quals [CL.BindQ v xs'])

        -- concatMap (\x -> [ e | qs ]) xs
        -- => [ e | x <- xs, qs ]
        CL.Lam _ v (CL.Comp _ e (CL.Quals qs)) ->
          resugar $ CL.Comp t e (CL.Quals (CL.BindQ v xs' : qs))
          
        _ -> cm

    CL.AppE2 t p1 e1 e2 -> CL.AppE2 t p1 (resugar e1) (resugar e2)
    CL.BinOp t op e1 e2 -> CL.BinOp t op (resugar e1) (resugar e2)
    CL.Lam t v e1 -> CL.Lam t v (resugar e1)
    
    CL.If t ce te ee -> CL.If t (resugar ce) (resugar te) (resugar ee)
    constant@(CL.Lit _ _)    -> constant
    var@(CL.Var _ _) -> var
    comp@(CL.Comp t body (CL.Quals qs)) -> 
      if changed 
      then resugar $ CL.Comp t body' (CL.Quals qs')
      else CL.Comp t body' (CL.Quals qs)

      where -- We fold over the qualifiers and look for local rewrite possibilities
            resugarQual :: CL.Qual -> (Bool, [CL.Qual]) -> (Bool, [CL.Qual])
            resugarQual q (changedAcc, qsAcc) =
              case q of
                -- Eliminate unused bindings from guards
                -- qs, v <- guard p, qs'  => qs, p, qs' (when v \nelem fvs)
                CL.BindQ v (CL.AppE1 _ (CL.Prim1 CL.Guard _) p) | not $ v `S.member` fvs -> (True, CL.GuardQ p : qsAcc)
                _                                                            -> (changedAcc, q : qsAcc)
                
            (changed, qs') = foldr resugarQual (False, []) qs
            body' = resugar body
            fvs = CL.freeVars comp

translateType :: Type a -> T.Type
translateType UnitT = T.unitT
translateType BoolT = T.boolT
translateType CharT = T.stringT
translateType IntegerT = T.intT
translateType DoubleT = T.doubleT
translateType TextT = T.stringT
translateType (PairT t1 t2) = T.pairT (translateType t1) (translateType t2)
translateType (ListT t) = T.listT (translateType t)
translateType (ArrowT t1 t2) = (translateType t1) T..-> (translateType t2)

tableTypes :: Type [a] -> [T.Type]
tableTypes (ListT t) = fromTuples t
    where
        fromTuples :: Type a -> [T.Type]
        fromTuples (PairT t1 t2) = translateType t1 : fromTuples t2
        fromTuples t'              = [translateType t']
