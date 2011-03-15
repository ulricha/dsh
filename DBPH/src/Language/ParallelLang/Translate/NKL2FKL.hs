{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.Translate.NKL2FKL where

import qualified Language.ParallelLang.FKL.Data.FKL as F
import qualified Language.ParallelLang.NKL.Data.NKL as N
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Config
import Language.ParallelLang.Translate.TransM
import Language.ParallelLang.FKL.ProcessFKL

import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Common.Impossible
import Language.ParallelLang.Common.Data.Type
import Language.ParallelLang.Common.Data.Prelude(preludeEnv)

import qualified Data.Map as M
import qualified Data.List as L

import Control.Applicative

flatTransform :: ([N.Expr], N.Expr) -> TransM ([F.Expr Type], F.Expr Type)
flatTransform (fs, e) = do
                           -- Transform function declarations
                           fs'  <- mapM transform fs
                           -- Lift all declared functions
                           fs'' <- mapM liftFunction fs'
                           let fs''' = map (\(_, _, _, fn) -> fn) fs''
                           e'   <- transform e
                           -- let funs = collectLifted (e':(concat fs'''))
                           -- let liftFun = generateHigherLifted (M.fromList $ primFuns ++ funArgs) funs
                           return (concat fs''', e')
                           
generateHigherLifted :: M.Map String ([String], Type) -> [(String, [Int])] -> [F.Expr Type]
generateHigherLifted args l = concat $ [map (liftFunD x (args M.! x)) (filter (>1) is) | (x, is) <- l]

liftFunD :: String -> ([String], Type) -> Int -> F.Expr Type
liftFunD n (args, t) d = let (tys, rt) = splitTypeArgsRes t
                             argTy = zip args $ map (liftTypeN d) tys
                             f = F.App (liftType rt) (F.Var (liftType t) n 1) [extractF (F.Var ty v 0) (intF (d -1)) | (v, ty) <- argTy]
                          in F.Fn (liftTypeN d t) n d args $ insertF f (F.Var (liftTypeN d $ head tys) (head args) 0) (intF $ d-1)

transform :: N.Expr -> TransM (F.Expr Type)
transform (N.Nil t) = pure $ F.Nil t
transform (N.App t e1 es) = F.App t <$> (transform e1) <*> mapM transform es
transform (N.Fn t n l args e) = F.Fn t n l args <$> transform e
transform (N.Let t n e1 e2) = F.Let t n <$> transform e1 <*> transform e2
transform (N.If t e1 e2 e3) = F.If t <$> transform e1 <*> transform e2 <*> transform e3
transform (N.BinOp t o e1 e2) = F.BinOp t o <$> transform e1 <*> transform e2
transform (N.Const t v) = pure $ F.Const t v
transform (N.Var t x l) = pure $ F.Var t x l
transform (N.IterG t n e1 e2 e3) = transform $ N.App t (N.Var (t .-> listT boolT .-> t) "restrict" 0) 
                                                    [N.Iter (listT boolT) n e1 e2,
                                                     N.Iter t n e1 e3]
                                    
transform (N.Iter t n e1 e2) = do
                                e1' <- transform e1
                                e2' <- withIterVar n $ transform e2
                                r <- flatten n e1' e2'
                                case typeOf r == t of
                                    True -> pure r
                                    False -> error "Transformation wrecked the type"
transform (N.Proj t l e1 i) = flip (F.Proj t l) i <$> transform e1

flatten :: String -> F.Expr Type -> F.Expr Type -> TransM (F.Expr Type)
flatten i e1 eb = do
                    o <- withOpt RedRepl
                    fVars <- getLetVars
                    if o then do
                                if (not $ isSimpleExpr e1)
                                  then do
                                         fv <- getFreshVar
                                         let v = F.Var (typeOf e1) fv 0
                                         e' <- flatten i v eb
                                         return $ letF fv e1 e'
                                  else if (not $ isSimpleExpr eb) && (not $ dependsOnVar (i:fVars) eb)
                                         then do
                                               fv <- getFreshVar
                                               let t = typeOf eb
                                               e' <- flatten' i e1 (F.Var t fv 0)
                                               return $ letF fv eb e'
                                         else flatten' i e1 eb
                                             
                         else flatten' i e1 eb
    
flatten' :: String -> F.Expr Type -> F.Expr Type -> TransM (F.Expr Type)
flatten' i e1 (F.Labeled s e) = F.Labeled s <$> flatten' i e1 e
flatten' i e1 (F.Var t x d) | i == x = return e1
                            | otherwise = do 
                                           isLet <- isLetVar x
                                           case isLet of
                                             True -> return $ F.Var (listT t) x d
                                             False -> do
                                                        isIter <- isIterVar x
                                                        case isIter of
                                                            True -> return $ distF (F.Var t x d) e1
                                                            False -> return $ promoteF (F.Var t x d) e1
flatten' _ e1 (F.Const t v) = return $ promoteF (F.Const t v) e1
flatten' _ d (F.Nil t) = return $ promoteF (F.Nil t) d
flatten' i d (F.App _ (F.Var _ "promote" 0) [arg1, arg2]) =
                                do
                                    arg2' <- flatten i d arg2
                                    return $ promoteF arg1 arg2'
flatten' i e1 (F.App t (F.Var ft x d) es) = F.App (liftType t) (F.Var (liftType ft) x $ d + 1) <$> mapM (flatten i e1) es
flatten' i e1 (F.Let ty v eb e) = do 
                                o <- withOpt LetOpt
                                case o of
                                    True -> do
                                             tB <- flatten i e1 eb
                                             F.Let (listT ty) v tB <$> (withLetVar v $ flatten i e1 e)
                                    False -> do
                                              t <- getFreshVar
                                              it <- getFreshVar
                                              tb <- flatten i e1 eb
                                              let t1 = typeOf eb
                                              let t2 = typeOf e
                                              bd <- withIterVar it $ flatten it 
                                                                        (rangeF (intF 1) (lengthF $ varF (listT t1) t)) 
                                                                        (substitute v (indexF (varF (listT t1) t)  (varF intT it)) 
                                                                            $ substitute i (indexF e1 (varF intT it)) e)
                                              return $ F.Let (listT t2) t tb bd
flatten' i d (F.If ty e1 e2 e3) = do
                                m <- getFreshVar
                                t <- getFreshVar
                                e <- getFreshVar
                                k <- getFreshVar
                                e1' <- flatten i d e1
                                e2' <- withIterVar k $ flatten k (restrictF d (F.Var (listT boolT) m 0)) (substitute i (F.Var ty k 0) e2)
                                e3' <- withIterVar k $ flatten k (restrictF d $ notF $ F.Var (listT boolT) m 0) (substitute i (F.Var ty k 0) e3)
                                return $ F.Let (listT ty) m e1'
                                            $ F.Let (listT ty) t e2'
                                                $ F.Let (listT ty) e e3' 
                                                    $ combineF (F.Var (listT boolT) m 0) (F.Var (listT ty) t 0) (F.Var (listT ty) e 0)
flatten' _ _ (F.Fn _ _ _ _ _) = error "Functions cannot yet occur in lists"-- $impossible
flatten' _ _ (F.App _ _ _) = error "Unsupported form of application" -- $impossible
flatten' i d (F.BinOp t (Op o n) e1 e2) = do
                                          e1' <- flatten i d e1
                                          e2' <- flatten i d e2
                                          return $ F.BinOp (listT t) (Op o (n + 1)) e1' e2'
flatten' i d (F.Proj t l e1 el) = do
                                e1' <- flatten i d e1
                                return $ F.Proj (listT t) (l + 1) e1' el

group' :: Eq a => [(a, b)] -> [(a, [b])]
group' a = map (\(k, v) -> (head k, v)) $ map (\ls -> (map fst ls, map snd ls)) $  L.groupBy (\(x, _) (y, _) -> x == y) a

collectLifted :: [F.Expr Type] -> [(String, [Int])]
collectLifted es = group' $ L.nub $ filter (\(n, i) -> (not $ isPrimitive n) || i > 1) $ concatMap collectFns es

collectFns :: (F.Expr Type) -> [(String, Int)]
collectFns (F.Labeled _ e) = collectFns e
collectFns (F.App _ e1 es) = collectFns e1 ++ concatMap collectFns es
collectFns (F.Nil _) = []
collectFns (F.Fn _ _ _ _ e1) = collectFns e1
collectFns (F.Let _ _ e1 e2) = collectFns e1 ++ collectFns e2
collectFns (F.If _ e1 e2 e3) = collectFns e1 ++ collectFns e2 ++ collectFns e3
collectFns (F.BinOp _ (Op o i) e1 e2) = (:) (o, i) $ collectFns e1 ++ collectFns e2
collectFns (F.Var _ _ 0) = []
collectFns (F.Var _ x i) = [(x, i)]
collectFns (F.Const _ _) = []
collectFns (F.Proj _ _ e _) = collectFns e 

liftFunction :: (F.Expr Type) -> TransM (String, Type, [String], [F.Expr Type])
liftFunction f@(F.Fn t n _ [] _)   = return (n, t, [], [f])
liftFunction f@(F.Fn t x 0 args e) = 
                                  do
                                    o <- withOpt FnOpt
                                    if o
                                     then do
                                            let tys = extractFnArgs t
                                            let v = head args
                                            let r = rangeF (intF 1) $ lengthF $ varF (head tys) v
                                            i <- getFreshVar
                                            e' <- withIterVar i $ foldr withLetVar (flatten i r e) args 
                                            return (x, t, args, [f, F.Fn (liftType t) x 1 args e'])
                                     else do
                                            let v = head args
                                            let tys = extractFnArgs t
                                            let r = rangeF (intF 1) $ lengthF $ varF (head tys) v
                                            let args' = zip args tys
                                            i <- getFreshVar
                                            let rep = \(var, ty) -> F.App (listT ty) (F.Var (listT ty .-> intT .-> ty) "index" 0) [F.Var (listT ty) var 0, F.Var intT i 0]
                                            e' <- withIterVar i $ flatten i r $ foldr (\var b -> substitute (fst var) (rep var) b) e args'
                                            return (x, t, args, [f, F.Fn (liftType t) x 1 args e'])
liftFunction _ = $impossible 
                                     
                                     
isPrimitive :: String -> Bool
isPrimitive f = elem f $ map fst primFuns

primFuns :: [(String, ([String], Type))]
primFuns = [(f, (args, unsafeInstantiate $ preludeEnv f)) | (f, args) <- primFunsArgs]

primFunsArgs :: [(String, [String])]
primFunsArgs = [("+",     ["e1", "e2"]),
          ("-",     ["e1", "e2"]),
          ("/",     ["e1", "e2"]),
          ("*",     ["e1", "e2"]),
          ("&&",    ["e1", "e2"]),
          ("||",    ["e1", "e2"]),
          (":", ["hd", "tl"]),
          ("not", ["e1"]),
--        (  "build", ["e1", "e2"]
          ("index", ["e1", "e2"]),
          ("length", ["e1"]),
          ("dist",   ["e1", "e2"]),
          ("range",  ["e1", "e2"]),
          ("restrict", ["e1", "e2"]),
          ("reduce", ["e1"]),
          ("combine", ["e1", "e2", "e3"]),
          ("promote", ["e1", "e2"]),
          ("bPermute", ["e1", "e2"]),
          ("(,)", ["e1", "e2"]),
          ("(,,)", ["e1", "e2", "e3"]),
          ("(,,,)", ["e1", "e2", "e3", "e4"])]

dependsOnVar :: [String] -> F.Expr Type -> Bool
dependsOnVar v (F.Labeled _ e) = dependsOnVar v e
dependsOnVar v (F.App _ e1 es) = dependsOnVar v e1 || (or $ map (dependsOnVar v) es)
dependsOnVar _ (F.Nil _) = False
dependsOnVar v (F.Fn _ _ _ args e1) = let n = v L.\\ args 
                                     in case n of
                                            [] -> False
                                            _  -> dependsOnVar n e1
dependsOnVar v (F.Let _ x e1 e2) | x `elem` v = dependsOnVar v e1
                               | otherwise  = dependsOnVar v e1 || dependsOnVar v e2
dependsOnVar v (F.If _ e1 e2 e3) = dependsOnVar v e1 || dependsOnVar v e2 || dependsOnVar v e3
dependsOnVar v (F.BinOp _ _ e1 e2) = dependsOnVar v e1 || dependsOnVar v e2
dependsOnVar v (F.Var _ x _) = x `elem` v
dependsOnVar _ (F.Const _ _) = False
dependsOnVar v (F.Proj _ _ e _) = dependsOnVar v e