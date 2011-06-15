{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.CompileFlattening (toNKL) where

import Database.DSH.Impossible

import qualified Language.ParallelLang.NKL.Data.NKL as NKL
import qualified Language.ParallelLang.Common.Data.Val as V
import qualified Language.ParallelLang.Common.Data.Type as T
import qualified Language.ParallelLang.Common.Data.Op as O

import Database.DSH.Data as D
import Database.DSH.Impossible (impossible)
import Database.HDBC
import Data.Text (unpack)

import Control.Monad.State
import Control.Applicative

import Data.Char (toLower)
{-
N monad, version of the state monad that can provide fresh variable names.
-}
type N conn = StateT (conn, Int) IO

-- | Provide a fresh identifier name during compilation
freshVar :: N conn Int
freshVar = do
             (c, i) <- get
             put (c, i + 1)
             return i

prefixVar :: Int -> String
prefixVar i = "*dshVar*" ++ show i

-- | Get from the state the connection to the database                
getConnection :: IConnection conn => N conn conn
getConnection = do
                 (c, _) <- get
                 return c

toNKL :: IConnection conn => conn -> Exp -> IO NKL.Expr
toNKL c e = runN c $ translate e

-- | Execute the transformation computation. During
-- compilation table information can be retrieved from
-- the database, therefor the result is wrapped in the IO
-- Monad.      
runN :: IConnection conn => conn -> N conn a -> IO a
runN c  = liftM fst . flip runStateT (c, 1)


translate :: IConnection conn => Exp -> N conn NKL.Expr
translate (UnitE _) = return $ NKL.Const T.unitT V.Unit
translate (BoolE b _) = return $ NKL.Const T.boolT $ V.Bool b
translate (CharE c _) = return $ NKL.Const T.stringT $ V.String [c]
translate (IntegerE i _) = return $ NKL.Const T.intT $ V.Int (fromInteger i)
translate (DoubleE d _) = return $ NKL.Const T.doubleT $ V.Double d 
translate (TextE t _) = return $ NKL.Const T.stringT $ V.String (unpack t) 
translate (VarE i ty) = return $ NKL.Var (ty2ty ty) (prefixVar i)
{-
translate (TupleE e1 e2 _) = do
                                c1 <- translate e1
                                c2 <- translate e2
                                let t1 = T.typeOf c1
                                let t2 = T.typeOf c2
                                return $ NKL.App (T.pairT t1 t2) (NKL.Var (t1 T..-> t2 T..-> T.pairT t1 t2) "(,,)") [c1, c2]
-}
translate (ListE es ty) = foldr (cons (ty2ty ty)) (NKL.Nil (ty2ty ty)) <$> mapM translate es
translate (LamE f ty) = do
                        v <- freshVar
                        let (ArrowT t1 _) = ty
                        f' <- translate $ f (VarE v t1)
                        return $ NKL.Lam (ty2ty ty) (prefixVar v) f' 
translate (AppE1 Fst e1 ty) = do
                                c1 <- translate e1
                                let t1 = T.typeOf c1
                                return $ NKL.Proj (head $ T.tupleComponents t1) 0 c1 1
translate (AppE1 Snd e1 ty) = do
                                c1 <- translate e1
                                let t1 = T.typeOf c1
                                return $ NKL.Proj (head $ T.tupleComponents t1) 0 c1 2
translate (AppE1 f e1 ty) = do 
                                c1 <- translate e1
                                return $ NKL.App (ty2ty ty) (NKL.Var (T.typeOf c1 T..-> ty2ty ty) (map toLower $ show f)) c1
translate (AppE2 Map e1 e2 ty) = do
                                  c1 <- translate e1
                                  c2 <- translate e2
                                  n <- freshVar
                                  let tEl = T.unliftType (T.typeOf c2)
                                  let tr = T.extractFnRes (T.typeOf c1)
                                  return $ NKL.Iter (ty2ty ty) (prefixVar n) c2 (NKL.App tr c1 (NKL.Var tEl (prefixVar n)))

{-
translate (AppE2 Span f e t@(TupleT t1 t2)) = transformE $ TupleE (AppE2 TakeWhile f e t1) (AppE2 DropWhile f e t2) t
translate (AppE2 Break (LamE f _) e t@(TupleT t1 _)) = let notF = LamE (\x -> AppE1 Not (f x) BoolT) $ ArrowT t1 BoolT
                                                 in transformE $ AppE2 Span notF e t
translate (AppE2 GroupWith gfn e ty@(ListT (ListT tel))) = do
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
translate (AppE2 D.Cons e1 e2 _) = do
                                            e1' <- transformE e1
                                            e2' <- transformE e2
                                            let (_ :=> t) = typeOf e1'
                                            return $ F.Cons ([] :=> list t) e1' e2'
translate (AppE2 Append e1 e2 t) = transformE (AppE1 Concat (ListE [e1, e2] (ListT t)) t)
translate (AppE2 Any f e _) = transformE $ AppE1 Or (AppE2 Map f e $ ListT BoolT) BoolT
translate (AppE2 All f e _) = transformE $ AppE1 And (AppE2 Map f e $ ListT BoolT) BoolT
translate (AppE2 Snoc e1 e2 t) = transformE (AppE2 Append e1 (ListE [e2] t) t)-}
translate (AppE2 f2 e1 e2 ty) = do
                                        let tr = ty2ty ty
                                        if elem f2 [Add, Sub, Mul, Div, Equ, Lt, Gt, Conj, Disj]
                                            then do
                                                   e1' <- translate e1
                                                   e2' <- translate e2
                                                   return $ NKL.BinOp tr (transformOp f2) e1' e2'
                                            else if elem f2 [Lte, Gte] 
                                                    then translate (AppE2 Disj (AppE2 Equ e1 e2 ty) (AppE2 (gtorlt f2) e1 e2 ty) ty)
                                                    else error "Application2: Not supported yet"
                                              {- do
                                                      e1' <- transformArg e1
                                                      e2' <- transformArg e2
                                                      let (_ :=> ta1) = typeOf e1'
                                                      let (_ :=> ta2) = typeOf e2'
                                                      return $ App ([] :=> tr) 
                                                                (App ([] :=> ta2 .-> tr) (transformF f2 (ta1 .-> ta2 .-> tr)) e1')
                                                                e2' -}
translate (AppE3 Cond e1 e2 e3 _) = do
                                             e1' <- translate e1
                                             e2' <- translate e2
                                             e3' <- translate e3
                                             return $ NKL.If (T.typeOf e2') e1' e2' e3'
{-
translate (AppE3 f3 e1 e2 e3 ty) = do
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
translate (VarE i ty) = return $ Var ([] :=> transformTy ty) $ prefixVar i
-}
translate e = error $ "CompileFlattening: Not supported: " ++ show e
gtorlt :: Fun2 -> Fun2
gtorlt Gte = Gt
gtorlt Lte = Lt
gtorlt _   = $impossible

cons :: T.Type -> NKL.Expr -> NKL.Expr -> NKL.Expr
cons t e1 e2 = NKL.BinOp t (O.Op ":" 0) e1 e2

isTuple :: String -> Maybe Int
isTuple ('(':xs) = let l = length xs
                       s = (replicate (l - 1) ',' ) ++ ")"
                    in if (xs == s) then Just (l - 1) else Nothing
isTuple _      = Nothing

ty2ty :: Type -> T.Type
ty2ty UnitT = T.unitT
ty2ty BoolT = T.boolT
ty2ty CharT = T.stringT 
ty2ty IntegerT = T.intT
ty2ty DoubleT = T.doubleT
ty2ty TextT = T.stringT
ty2ty (TupleT t1 t2) = T.pairT (ty2ty t1) (ty2ty t2)
ty2ty (ListT t) = T.listT (ty2ty t)
ty2ty (ArrowT t1 t2) = (ty2ty t1) T..-> (ty2ty t2)

-- | Translate the DSH operator to Ferry Core operators
transformOp :: Fun2 -> O.Op
transformOp Add = O.Op "+" 0
transformOp Sub = O.Op "-" 0
transformOp Mul = O.Op "*" 0
transformOp Div = O.Op "/" 0
transformOp Equ = O.Op "==" 0
transformOp Lt = O.Op "<" 0
transformOp Lte = O.Op "<=" 0
transformOp Gte = O.Op ">=" 0
transformOp Gt = O.Op ">" 0
transformOp Conj = O.Op "&&" 0
transformOp Disj = O.Op "||" 0
transformOp _ = $impossible 