-- | This module provides the flattening implementation of DSH.
module Database.DSH.Flattening (fromQ) where

import qualified Language.ParallelLang.NKL.Data.NKL as NKL
import qualified Language.ParallelLang.Common.Data.Val as V
import qualified Language.ParallelLang.Common.Data.Type as T
import qualified Language.ParallelLang.Common.Data.Op as O

import Database.DSH.Data as D
import Database.DSH.Impossible (impossible)
import Database.HDBC

import Control.Monad.State
import Control.Applicative

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

-- | Get from the state the connection to the database                
getConnection :: IConnection conn => N conn conn
getConnection = do
                 (c, _) <- get
                 return c


-- | Turn a given integer into a variable beginning with prefix "__fv_"                    
prefixVar :: Int -> String
prefixVar = ((++) "__fv_") . show
     
-- | Execute the transformation computation. During
-- compilation table information can be retrieved from
-- the database, therefor the result is wrapped in the IO
-- Monad.      
runN :: IConnection conn => conn -> N conn a -> IO a
runN c  = liftM fst . flip runStateT (c, 1)


fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q a) =  undefined -- evaluate c a >>= (return . fromNorm)

debugNKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugNKL = undefined

translate :: IConnection conn => Exp -> N conn NKL.Expr
translate (UnitE _) = return $ NKL.Const T.unitT V.Unit
translate (BoolE b _) = return $ NKL.Const T.boolT $ V.Bool b
translate (CharE c _) = error $ "Characters are not yet supported" 
translate (IntegerE i _) = return $ NKL.Const T.intT $ V.Int (fromInteger i)
translate (DoubleE d _) = error "Doubles are not yet supported" 
translate (TextE t _) = error "Texts are not yet supported" 
translate (TupleE e1 e2 _) = do
                                c1 <- translate e1
                                c2 <- translate e2
                                let t1 = T.typeOf c1
                                let t2 = T.typeOf c2
                                return $ NKL.App (T.pairT t1 t2) (NKL.Var (t1 T..-> t2 T..-> T.pairT t1 t2) "(,,)" 0) [c1, c2]
-- translate (ListE es ty) = foldr (cons (ty2ty ty)) (NKL.Nil (ty2ty ty)) $ map translate es
translate (AppE1 f1 e1 ty) = error "Application is not supported"
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
translate (AppE2 Snoc e1 e2 t) = transformE (AppE2 Append e1 (ListE [e2] t) t)
translate (AppE2 f2 e1 e2 ty) = do
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
translate (AppE3 Cond e1 e2 e3 _) = do
                                             e1' <- transformE e1
                                             e2' <- transformE e2
                                             e3' <- transformE e3
                                             let (_ :=> t) = typeOf e2'
                                             return $ If ([] :=> t) e1' e2' e3'
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
ty2ty CharT = error "Char type is not supported"
ty2ty IntegerT = T.intT
ty2ty DoubleT = error "Double type is not supported"
ty2ty TextT = error "Text type is not supported"
ty2ty (TupleT t1 t2) = T.pairT (ty2ty t1) (ty2ty t2)
ty2ty (ListT t) = T.listT (ty2ty t)
ty2ty (ArrowT t1 t2) = (ty2ty t1) T..-> (ty2ty t2)