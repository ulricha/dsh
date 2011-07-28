{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.Translate.Vec2Algebra (toAlgebra, toXML) where

import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.Common.Data.Val
import Database.Ferry.Algebra (double, string, int, bool, AVal(), intT, doubleT, stringT, natT, boolT, ATy(), nat, litTable, litTable', emptyTable, attachM, tagM, AlgNode(), AlgPlan(), initLoop, runGraph, withBinding, withContext, fromGam, notC, projM, crossM, unionM, selectM, proj, cross, eqJoinM, operM, dbTable, rownum) -- hiding (getLoop, Gam)
import qualified Database.Ferry.Algebra as A 
import Language.ParallelLang.FKL.Data.FKL
import qualified Language.ParallelLang.VL.Data.VectorTypes as T
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.VL.Data.Query
import Database.Ferry.Algebra.Render.XML hiding (XML, Graph)
import qualified Language.ParallelLang.Common.Data.Type as Ty
import Language.ParallelLang.VL.VectorOperations

import qualified Data.Map as M
import Control.Applicative hiding (Const)
import Control.Monad (liftM2)

import Language.ParallelLang.Common.Impossible


fkl2Alg :: Expr Ty.Type -> Graph Plan
fkl2Alg (Tuple _ es) = TupleVector <$> mapM fkl2Alg es
fkl2Alg (Table _ n cs ks) = makeTable n cs ks
fkl2Alg (Labeled _ e) = fkl2Alg e
fkl2Alg (Const t v) = val2Alg t v 
fkl2Alg (Nil (Ty.List t@(Ty.List _))) = NestedVector <$> (tagM "Nil" $ emptyTable [(descr, natT), (pos, natT)]) <*> fkl2Alg (Nil t)
fkl2Alg (Nil (Ty.List t)) = ValueVector <$> (tagM "Nil" $ emptyTable [(descr, natT), (pos, natT), (item1, convertType t)])
fkl2Alg (Nil _)                = error "Not a valid nil value"
fkl2Alg (BinOp _ (Op o l) e1 e2) | o == Cons = do
                                                p1 <- fkl2Alg e1
                                                p2 <- fkl2Alg e2
                                                if l 
                                                    then consLift p1 p2
                                                    else cons p1 p2
                                 | otherwise = do
                                                p1 <- fkl2Alg e1
                                                p2 <- fkl2Alg e2
                                                let (rt, extr) = if l 
                                                                   then (ValueVector, \e -> case e of {(ValueVector q) -> q; _ -> $impossible})
                                                                   else (PrimVal, \e -> case e of {(PrimVal q) -> q; _ -> $impossible})
                                                let q1 = extr p1
                                                let q2 = extr p2
                                                rt <$> (projM [(item1, resCol), (descr, descr), (pos, pos)] 
                                                    $ operM (show o) resCol item1 tmpCol 
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
fkl2Alg (PApp1 _ f arg) = fkl2Alg arg >>= case f of
                                           (LengthPrim _) -> lengthV 
                                           (LengthLift _) -> lengthLift
                                           (NotPrim _) -> notPrim 
                                           (NotVec _) -> notVec 
                                           (ConcatLift _) -> concatLift
fkl2Alg (PApp2 _ (Extract _) arg1 (Const _ (Int i))) = do
                                        e1 <- fkl2Alg arg1
                                        extract e1 i
fkl2Alg (PApp2 _ f arg1 arg2) = liftM2 (,) (fkl2Alg arg1) (fkl2Alg arg2) >>= uncurry fn 
    where
        fn = case f of
                (Extract _) -> $impossible
                (Dist _) -> dist
                (Dist_L _) -> distL
                (GroupWithS _) -> groupByS
                (GroupWithL _) -> groupByL
                (Index _) -> error "Index is not yet defined fkl2Alg"
                (Restrict _) -> restrict
                (BPermute _) -> bPermute
fkl2Alg (PApp3 _ (Insert _) arg1 arg2 (Const _ (Int i))) = liftM2 (,) (fkl2Alg arg1) (fkl2Alg arg2) >>= (\(x,y) -> insert x y i)
fkl2Alg (Var _ s) = fromGam s
fkl2Alg (Clo _ n fvs x f1 f2) = do
                                fv <- mapM (\(y, v) -> do {v' <- fkl2Alg v; return (y, v')}) fvs
                                return $ Closure n fv x f1 f2
fkl2Alg (AClo _ fvs x f1 f2) = do
                              ((n, v):fv) <- mapM (\(y, v) -> do {v' <- fkl2Alg v; return (y, v')}) fvs
                              return $ AClosure n v 1 fv x f1 f2 
fkl2Alg (CloApp _ c arg) = do
                             (Closure _ fvs x f1 _) <- fkl2Alg c
                             arg' <- fkl2Alg arg
                             withContext [] undefined $ foldl (\e (y,v') -> withBinding y v' e) (fkl2Alg f1) ((x, arg'):fvs)
fkl2Alg (CloLApp _ c arg) = do
                              (AClosure n v 1 fvs x _ f2) <- fkl2Alg c
                              arg' <- fkl2Alg arg
                              withContext [] undefined $ foldl (\e (y,v') -> withBinding y v' e) (fkl2Alg f2) ((n, v):(x, arg'):fvs)
-- fkl2Alg e                 = error $ "unsupported: " ++ show e

makeTable :: String -> [Column Ty.Type] -> [Key] -> Graph Plan
makeTable n cs ks = do
                     table <- dbTable n (renameCols cs) ks
                     t' <- attachM descr natT (nat 1) $ rownum pos (head ks) Nothing table
                     cs' <- mapM (\(_, i) -> ValueVector <$> proj [(descr, descr), (pos, pos), (item1, "item" ++ show i)] t') $ zip cs [1..]
                     return $ foldl1 (\x y -> TupleVector [y,x]) $ reverse cs'
  where
    renameCols :: [Column Ty.Type] -> [A.Column]
    renameCols xs = [A.NCol cn [A.Col i $ algTy t]| ((cn, t), i) <- zip xs [1..]]

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
                     (Closure _ _ _ _ _) -> error "Functions cannot appear as a result value"
                     (AClosure _ _ _ _ _ _ _) -> error "Function cannot appear as a result value"
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
    


val2Alg :: Ty.Type -> Val -> Graph Plan
val2Alg t (List es) = listToPlan t (zip (repeat 1) es)
val2Alg _t v = PrimVal <$> (tagM "constant" $ (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ val2Alg' v))
 where
  val2Alg' (Int i) = litTable (int $ fromIntegral i) item1 intT
  val2Alg' (Bool b) = litTable (bool b) item1 boolT
  val2Alg' Unit     = litTable (int (-1)) item1 intT  
  val2Alg' (String s) = litTable (string s) item1 stringT
  val2Alg' (Double d) = litTable (double d) item1 doubleT
  val2Alg' (List _) = $impossible 

listToPlan :: Ty.Type -> [(Integer, Val)] -> Graph Plan
listToPlan (Ty.List t@(Ty.List _)) [] = do
                                               d <- emptyTable [("iter", natT), ("pos", natT)]
                                               v <- listToPlan t []
                                               return $ NestedVector d v
listToPlan (Ty.List t@(Ty.List _)) vs = do
                                          let (vals, rec) = unzip [([nat i, nat p], zip (repeat p) es) | (p, (i, List es)) <- zip [1..] vs]
                                          d <- litTable' vals  [("iter", natT), ("pos", natT)]
                                          v <- listToPlan t $ concat rec
                                          return $ NestedVector d v                                                    
listToPlan (Ty.List t) [] = ValueVector <$> emptyTable [("iter", natT), ("pos", natT), ("item1", algTy t)]
listToPlan (Ty.List t) vs = ValueVector <$> litTable' [[nat i, nat p, toAlgVal v] | (p, (i, v)) <- zip [1..] vs] [("iter", natT), ("pos", natT), ("item1", algTy t)]
listToPlan _ _ = $impossible "Not a list value or type"
       
algTy :: Ty.Type -> ATy
algTy (Ty.Int) = intT
algTy (Ty.Double) = doubleT
algTy (Ty.Bool) = boolT
algTy (Ty.String) = stringT
algTy (Ty.Unit) = intT
algTy _               = $impossible "Not a primitive type"

toAlgVal :: Val -> AVal
toAlgVal (Int i) = int $ fromIntegral i
toAlgVal (Bool b) = bool b
toAlgVal Unit = int (-1)
toAlgVal (String s) = string s
toAlgVal (Double d) = double d
toAlgVal _ = $impossible "Not a primitive value"

-- | Construct a name that represents a lifted variable in the environment.                        
constrEnvName :: String -> Int -> String
constrEnvName x 0 = x
constrEnvName x i = x ++ "<%>" ++ show i

intFromVal :: Expr T.VType -> Int
intFromVal (Const _ (Int i)) = i
intFromVal x                 = error $ "intFromVal: not an integer: " ++ show x
