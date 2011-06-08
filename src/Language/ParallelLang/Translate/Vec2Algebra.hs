{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.Translate.Vec2Algebra (toAlgebra, toXML) where

import Language.ParallelLang.VL.Algebra
-- import Language.ParallelLang.VL.VectorOperations
import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.Common.Data.Val
import Database.Ferry.Algebra hiding (getLoop, withContext, Gam)
import Language.ParallelLang.FKL.Data.FKL
import qualified Language.ParallelLang.VL.Data.VectorTypes as T
import Language.ParallelLang.Common.Data.Op
-- import qualified Language.ParallelLang.Common.Data.Type as U
import Language.ParallelLang.VL.Data.Query
import Database.Ferry.Algebra.Render.XML hiding (XML, Graph)
import qualified Language.ParallelLang.Common.Data.Type as Ty
import Language.ParallelLang.VL.VectorOperations

import qualified Data.Map as M
import Control.Applicative hiding (Const)

import Language.ParallelLang.Common.Impossible


fkl2Alg :: Expr Ty.Type -> Graph Plan
fkl2Alg (Labeled s e) = fkl2Alg e
fkl2Alg (Const _ v) = PrimVal <$> (tagM "constant" $ (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ val2Alg v))
fkl2Alg (Nil (Ty.TyC "List" [t@(Ty.TyC "List" _)])) = NestedVector <$> (tagM "Nil" $ emptyTable [(descr, natT), (pos, natT)]) <*> fkl2Alg (Nil t)
fkl2Alg (Nil (Ty.TyC "List" [t])) = ValueVector <$> (tagM "Nil" $ emptyTable [(descr, natT), (pos, natT), (item1, convertType t)])
fkl2Alg (Nil _)                = error "Not a valid nil value"
fkl2Alg (BinOp _ (Op o l) e1 e2) | o == ":" = do
                                                p1 <- fkl2Alg e1
                                                p2 <- fkl2Alg e2
                                                case l of
                                                    0 -> cons p1 p2
                                                    1 -> consLift p1 p2
                                                    _ -> error "This level of liftedness should have been eliminated"
                                 | otherwise = do
                                                p1 <- fkl2Alg e1
                                                p2 <- fkl2Alg e2
                                                let (rt, extr) = case l of
                                                                   0 -> (PrimVal, \e -> case e of {(PrimVal q) -> q; _ -> $impossible})
                                                                   1 -> (ValueVector, \e -> case e of {(ValueVector q) -> q; _ -> $impossible})
                                                                   _ -> error "This level of liftedness should have been eliminated"
                                                let q1 = extr p1
                                                let q2 = extr p2
                                                rt <$> (projM [(item1, resCol), (descr, descr), (pos, pos)] 
                                                    $ operM o resCol item1 tmpCol 
                                                        $ eqJoinM pos pos' (return q1) 
                                                            $ proj [(tmpCol, item1), (pos', pos)] q2)
fkl2Alg (Proj _ _ e n) = do
                          (TupleVector es) <- fkl2Alg e
                          return $ es !! (n - 1)
fkl2Alg (If t eb e1 e2) | Ty.listDepth t == 0 = do
                             (PrimVal qb) <- fkl2Alg eb
                             (PrimVal q1) <- fkl2Alg e1
                             (PrimVal q2) <- fkl2Alg e2
                             b <- proj [(tmpCol, item1)] qb
                             qr <- projM [(descr, descr), (pos, pos), (item1, item1)] $ 
                                       selectM  tmpCol $ 
                                           unionM (cross q1 b) $ 
                                              crossM (return q2) $ 
                                                  projM [(tmpCol, resCol)] $ notC resCol tmpCol b
                             return (PrimVal qr)
                        | Ty.listDepth t == 1 = do
                             (PrimVal qb)     <- fkl2Alg eb
                             (ValueVector q1) <- fkl2Alg e1
                             (ValueVector q2) <- fkl2Alg e2
                             b <- proj [(tmpCol, item1)] qb
                             qr <- projM [(descr, descr), (pos, pos), (item1, item1)] $ 
                                   selectM  tmpCol $ 
                                       unionM (cross q1 b) $ 
                                           crossM (return q2) $ 
                                               projM [(tmpCol, resCol)] $ notC resCol tmpCol b
                             return (ValueVector qr)
                        | otherwise = error "vec2Alg: Can't translate if construction"
fkl2Alg (Let _ s e1 e2) = do
                            e' <- fkl2Alg e1
                            e1' <- tagVector s e'
                            withBinding s e1' $ fkl2Alg e2
fkl2Alg (Var _ s) = fromGam s
fkl2Alg (App _ (Var _ x) args) = case x of
                                    "dist" -> do
                                                [e1, e2] <- mapM fkl2Alg args
                                                dist e1 e2
                                    "dist_L" -> do
                                                [e1, e2] <- mapM fkl2Alg args
                                                distL e1 e2
                                    "index" -> undefined
                                    "length" -> undefined
                                    "restrict" -> undefined
                                    "not" -> undefined
                                    "combine" -> undefined
                                    "insert" -> undefined
                                    "extract" -> undefined
                                    "bPermute" -> undefined
                                    

toAlgebra :: Expr Ty.Type -> AlgPlan Plan
toAlgebra e = runGraph initLoop (fkl2Alg e)

toXML :: AlgPlan Plan -> Query XML
toXML (g, r, ts) = case r of
                     (PrimVal r') -> PrimVal (XML r' $ toXML' withItem r')
                     (TupleVector rs)   -> TupleVector $ map (\r' -> toXML (g, r', ts)) rs
                     (DescrVector r') -> DescrVector (XML r' $ toXML' withoutItem r')
                     (ValueVector r') -> ValueVector (XML r' $ toXML' withItem r')
                     (NestedVector r' rs) -> NestedVector (XML r' $ toXML' withoutItem r') $ toXML (g, rs, ts)
                     (PropVector _) -> error "Prop vectors should only be used internally and never appear in a result"
                     (Closure _ _ _ _) -> error "Functions cannot appear as a result value"
                     (AClosure _ _ _) -> error "Function cannot appear as a result value"
--                     (UnEvaluated _) -> error "A not evaluated function can not occur in the query result"
    where
        item :: Element ()
        item = [attr "name" $ "item1", attr "new" "false", attr "function" "item", attr "position" "1"] `attrsOf` xmlElem "column"
        withItem, withoutItem :: [Element ()]
        withItem = [iterCol, posCol, item]
        withoutItem = [iterCol, posCol]
        nodeTable = M.fromList $ map (\(a, b) -> (b, a)) $ M.toList g
        toXML' :: [Element ()] -> AlgNode -> String
        toXML' cs n = show $ document $ mkXMLDocument $ mkPlanBundle $ 
                        runXML False M.empty M.empty $
                            mkQueryPlan Nothing (xmlElem "property") $ 
                                runXML True nodeTable ts $ serializeAlgebra cs n
    


val2Alg :: Val -> Graph AlgNode
val2Alg (Int i) = litTable (int $ fromIntegral i) item1 intT
val2Alg (Bool b) = litTable (bool b) item1 boolT
val2Alg Unit     = litTable (int (-1)) item1 intT  
val2Alg (String s) = litTable (string s) item1 stringT
val2Alg (Double d) = litTable (double d) item1 doubleT 

vec2Alg :: Expr T.VType -> Graph Plan
vec2Alg (Labeled _ e) = vec2Alg e
{-
vec2Alg (Const _ v) = PrimVal <$> (tagM "constant" $ (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ val2Alg v))
vec2Alg (Nil (T.Tagged vt t)) = case T.nestingDepth vt of
                            0 -> error "Invalid vector type for a Nil value"
                            1 -> ValueVector <$> (tagM "Nil" $ emptyTable [(descr, natT), (pos, natT), (item1, convertType $ U.unliftType t)])
                            n -> NestedVector <$> (tagM "Nil" $ emptyTable [(descr, natT), (pos, natT)]) <*> (tagVector "NilR" $ vec2Alg (Nil (T.Tagged (T.NestedVector (n - 1)) (U.unliftType t))))
vec2Alg (Nil _) = error "Nil without tagged type not supported"
vec2Alg (BinOp _ (Op o l) e1 e2) | o == ":" = error "Cons operations should have been desugared"
                                 | otherwise = do
                                                p1 <- vec2Alg e1
                                                p2 <- vec2Alg e2
                                                let (rt, extr) = case l of
                                                                  0 -> (PrimVal, \e -> case e of {(PrimVal q) -> q; _ -> $impossible})
                                                                  1 -> (ValueVector, \e -> case e of {(ValueVector q) -> q; _ -> $impossible})
                                                                  _ -> error "This level of liftedness should have been elimated"
                                                let q1 = extr p1
                                                let q2 = extr p2
                                                rt <$> (projM [(item1, resCol), (descr, descr), (pos, pos)] 
                                                    $ operM o resCol item1 tmpCol 
                                                        $ eqJoinM pos pos' (return q1) 
                                                            $ proj [(tmpCol, item1), (pos', pos)] q2)
vec2Alg (Proj _ _ e n) = do
                            (TupleVector es) <- vec2Alg e
                            return $ es !! (n - 1)        
vec2Alg (If t eb e1 e2) | t == T.pValT = do
                                            (PrimVal qb) <- vec2Alg eb
                                            (PrimVal q1) <- vec2Alg e1
                                            (PrimVal q2) <- vec2Alg e2
                                            b <- proj [(tmpCol, item1)] qb
                                            qr <- projM [(descr, descr), (pos, pos), (item1, item1)] $ 
                                                    selectM  tmpCol $ 
                                                        unionM (cross q1 b) $ 
                                                            crossM (return q2) $ 
                                                                projM [(tmpCol, resCol)] $ notC resCol tmpCol b
                                            return (PrimVal qr)
                        | T.nestingDepth t == 1 = do
                                                 (PrimVal qb) <- vec2Alg eb
                                                 (ValueVector q1) <- vec2Alg e1
                                                 (ValueVector q2) <- vec2Alg e2
                                                 b <- proj [(tmpCol, item1)] qb
                                                 qr <- projM [(descr, descr), (pos, pos), (item1, item1)] $ 
                                                         selectM  tmpCol $ 
                                                             unionM (cross q1 b) $ 
                                                                 crossM (return q2) $ 
                                                                     projM [(tmpCol, resCol)] $ notC resCol tmpCol b
                                                 return (ValueVector qr)
                         | otherwise = error "vec2Alg: Can't translate if construction"
vec2Alg (Let _ s e1 e2) = do
                            e1' <- tagVector s $ vec2Alg e1
                            withBinding s e1' (vec2Alg e2)
vec2Alg (Var _ s) = fromGam $ constrEnvName s i
vec2Alg (App _ (Var _ x i) args) = case x of
                                    "not" -> do
                                               let [e] = map vec2Alg args
                                               notA e
                                    "outer" -> do 
                                                let [e] = map vec2Alg args
                                                outer e
                                    "distPrim" -> do 
                                                   let [e1, e2] = map vec2Alg args
                                                   distPrim e1 e2
                                    "distDesc" -> do 
                                                   let [e1, e2] = map vec2Alg args
                                                   distDesc e1 e2
                                    "distLift" -> do 
                                                    let [e1, e2] = map vec2Alg args
                                                    distLift e1 e2
                                    "propagateIn" -> do 
                                                      let [e1, e2] = map vec2Alg args
                                                      propagateIn e1 e2
                                    "rename" -> do 
                                                 let [e1, e2] = map vec2Alg args
                                                 rename e1 e2
                                    "attach" -> do 
                                                 let [e1, e2] = map vec2Alg args
                                                 attachV e1 e2
                                    "singletonPrim" -> do 
                                                        let [e1] = map vec2Alg args
                                                        singletonPrim e1
                                    "singletonVec" -> do 
                                                       let [e1] = map vec2Alg args
                                                       singletonVec e1
                                    "append" -> do 
                                                  let [e1, e2] = map vec2Alg args
                                                  append e1 e2
                                    "segment" -> do 
                                                  let [e1] = map vec2Alg args
                                                  segment e1
                                    "restrictVec" -> do 
                                                      let [e1, e2] = map vec2Alg args
                                                      restrictVec e1 e2
                                    "combineVec" -> do 
                                                     let [e1, e2 ,e3] = map vec2Alg args
                                                     combineVec e1 e2 e3
                                    "bPermute" -> do 
                                                    let [e1, e2] = map vec2Alg args
                                                    bPermuteVec e1 e2
                                    "extract" -> do 
                                                    let [e1, e2] = args
                                                    extract (vec2Alg e1) (intFromVal e2)
                                    "insert" -> do 
                                                  let [e1, e2, e3] = args
                                                  insert (vec2Alg e1) (vec2Alg e2) (intFromVal e3)
                                    _        -> do
                                                 v <- fromGam (constrEnvName x i)
                                                 case v of
--                                                     UnEvaluated v' -> vec2Alg (App t v' args)
                                                     _              -> error $ "vec2Alg application: Not a function: " ++ show v
-}
{-
vec2Alg (App _ (Fn _ _ _ avs e) args) = do
                                         args' <- mapM vec2Alg args
                                         foldr (\(x, a) ex -> withBinding x a ex) (vec2Alg e) (zip avs args')
-}
vec2Alg _ = error "Not defined yet"
{-
data Expr t where
    App   :: t -> Expr t -> [Expr t] -> Expr t-- | Apply multiple arguments to an expression
    Fn    :: t -> String -> Int -> [String] -> Expr t -> Expr t -- | A function has a name (and lifted level), some arguments and a body
-}

-- | Construct a name that represents a lifted variable in the environment.                        
constrEnvName :: String -> Int -> String
constrEnvName x 0 = x
constrEnvName x i = x ++ "<%>" ++ show i

intFromVal :: Expr T.VType -> Int
intFromVal (Const _ (Int i)) = i
intFromVal x                 = error $ "intFromVal: not an integer: " ++ show x
