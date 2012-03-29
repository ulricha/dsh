{-# LANGUAGE TemplateHaskell, RelaxedPolyRec, TupleSections #-}
module Language.ParallelLang.Translate.Vec2Algebra (toPFAlgebra, toXML, toX100Algebra, toX100String, toX100File) where

-- FIXME this should import a module from TableAlgebra which defines 
-- common types like schema info and abstract column types.
import Database.Algebra.Pathfinder(PFAlgebra)

import Database.Algebra.X100.Data(X100Algebra)
import Database.Algebra.X100.Data.Create(dummy)
import Database.Algebra.X100.Serialize
import Database.Algebra.X100.Render

import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.VL.PathfinderVectorPrimitives()
import Language.ParallelLang.VL.X100VectorPrimitives()
import Database.Algebra.Dag.Common hiding (BinOp)
import Database.Algebra.Dag.Builder
import Language.ParallelLang.FKL.Data.FKL
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.VL.Data.Query
import Database.Algebra.Pathfinder.Render.XML hiding (XML, Graph)
import qualified Language.ParallelLang.Common.Data.Type as T
import qualified Language.ParallelLang.Common.Data.Val as V
import Language.ParallelLang.VL.VectorOperations



import Database.Algebra.Pathfinder(initLoop)

import qualified Data.Map as M
import Control.Monad (liftM, liftM2, liftM3)

import Language.ParallelLang.Common.Impossible

deTupleVal :: T.Type -> V.Val -> (V.Val, T.Type)
deTupleVal t v@(V.Int _) = (v, t)
deTupleVal t v@(V.Bool _) = (v, t)
deTupleVal t v@(V.String _) = (v, t)
deTupleVal t v@(V.Double _) = (v, t)
deTupleVal t v@(V.Unit) = (v, t)
deTupleVal (T.Pair t1 t2) (V.Pair e1 e2) = let (v1, t1') = deTupleVal t1 e1
                                               (v2, t2') = deTupleVal t2 e2
                                            in (V.Pair v1 v2, T.Pair t1' t2')
deTupleVal (T.List (T.Pair t1 t2)) (V.List xs) = let (l1, l2) = pushIn xs
                                                     (v1, t1') = deTupleVal (T.List t1) $ V.List l1
                                                     (v2, t2') = deTupleVal (T.List t2) $ V.List l2
                                                  in (V.Pair v1 v2, T.Pair t1' t2')
deTupleVal t1@(T.List t@(T.List _)) v@(V.List xs) | T.containsTuple t = deTupleVal (T.List $ transType t) $ V.List $ map (fst . (deTupleVal t)) xs
                                                  | otherwise       = (v, t1)
deTupleVal t@(T.List _) v = (v, t)
deTupleVal (T.Var _) _ = $impossible
deTupleVal (T.Fn _ _) _ = $impossible
deTupleVal _ _          = $impossible
    
pushIn :: [V.Val] -> ([V.Val], [V.Val])
pushIn ((V.Pair e1 e2):xs) = let (es1, es2) = pushIn xs in (e1:es1, e2:es2)
pushIn []                  = ([], [])
pushIn v                   = error $ "deTupler pushIn: Not a list of tuples: " ++ show v

transType :: T.Type -> T.Type
transType ot@(T.List t) | T.containsTuple t = case transType t of
                                                (T.Pair t1 t2) -> T.Pair (transType $ T.List t1) (transType $ T.List t2)
                                                t' -> T.List t'
                        | otherwise       = ot
transType (T.Pair t1 t2) = T.Pair (transType t1) (transType t2)
transType (T.Fn t1 t2)       = T.Fn (transType t1) (transType t2)
transType t                  = t

fkl2Alg :: (VectorAlgebra a) => Expr -> Graph a Plan
fkl2Alg (Table _ n cs ks) = tableRef n cs ks
fkl2Alg (Labeled _ e) = fkl2Alg e
fkl2Alg (Const t v) | T.containsTuple t = constructLiteral (transType t) (fst $ deTupleVal t v)
                    | otherwise = constructLiteral t v 
fkl2Alg (BinOp _ (Op o l) e1 e2) | o == Cons = do
                                                p1 <- fkl2Alg e1
                                                p2 <- fkl2Alg e2
                                                if l 
                                                    then consLift p1 p2
                                                    else cons p1 p2
                                 | otherwise = do
                                                p1 <- fkl2Alg e1
                                                p2 <- fkl2Alg e2
                                                binOp l o p1 p2
fkl2Alg (If _ eb e1 e2) = do 
                          eb' <- fkl2Alg eb
                          e1' <- fkl2Alg e1
                          e2' <- fkl2Alg e2
                          ifList eb' e1' e2'
fkl2Alg (PApp1 t f arg) = fkl2Alg arg >>= case f of
                                           (LengthPrim _) -> lengthV 
                                           (LengthLift _) -> lengthLift
                                           (NotPrim _) -> notPrim 
                                           (NotVec _) -> notVec 
                                           (ConcatLift _) -> concatLift
                                           (Sum _) -> sumPrim t
                                           (SumL _) -> sumLift
                                           (The _) -> the
                                           (TheL _) -> theL
                                           (Fst _) -> fstA
                                           (Snd _) -> sndA
                                           (FstL _) -> fstL
                                           (SndL _) -> sndL
                                           (Concat _) -> concatV
fkl2Alg (PApp2 _ f arg1 arg2) = liftM2 (,) (fkl2Alg arg1) (fkl2Alg arg2) >>= uncurry fn
    where
        fn = case f of
                (Dist _) -> \x y -> dist x y
                (Dist_L _) -> distL
                (GroupWithS _) -> groupByS
                (GroupWithL _) -> groupByL
                (SortWithS _) -> sortWithS
                (SortWithL _) -> sortWithL
                (Index _) -> error "Index is not yet defined fkl2Alg"
                (Restrict _) -> restrict
                (BPermute _) -> bPermute
                (Unconcat _) -> unconcatV
                (Pair _) -> \e1 e2 -> return $ TupleVector [e1, e2]
                (PairL _) -> \e1 e2 -> return $ TupleVector [e1, e2]
fkl2Alg (PApp3 _ (Combine _) arg1 arg2 arg3) = liftM3 (,,) (fkl2Alg arg1) (fkl2Alg arg2) (fkl2Alg arg3) >>= (\(x, y, z) -> combine x y z)
fkl2Alg (Var _ s) = fromGam s
fkl2Alg (Clo _ n fvs x f1 f2) = do
                                fv <- constructClosureEnv fvs
                                return $ Closure n fv x f1 f2
fkl2Alg (AClo _ n fvs x f1 f2) = do
                              v <- fromGam n
                              fv <- constructClosureEnv fvs
                              return $ AClosure n v 1 fv x f1 f2 
fkl2Alg (CloApp _ c arg) = do
                             (Closure _ fvs x f1 _) <- fkl2Alg c
                             arg' <- fkl2Alg arg
                             withContext [] undefined $ foldl (\e (y,v') -> withBinding y v' e) (fkl2Alg f1) ((x, arg'):fvs)
fkl2Alg (CloLApp _ c arg) = do
                              (AClosure n v 1 fvs x _ f2) <- fkl2Alg c
                              arg' <- fkl2Alg arg
                              withContext [] undefined $ foldl (\e (y,v') -> withBinding y v' e) (fkl2Alg f2) ((n, v):(x, arg'):fvs)

constructClosureEnv :: [String] -> Graph a [(String, Plan)]
constructClosureEnv [] = return []
constructClosureEnv (x:xs) = liftM2 (:) (liftM (x,) $ fromGam x) (constructClosureEnv xs)

toPFAlgebra :: Expr -> AlgPlan PFAlgebra Plan
toPFAlgebra e = runGraph initLoop (fkl2Alg e)

toX100Algebra :: Expr -> AlgPlan X100Algebra Plan
toX100Algebra e = runGraph dummy (fkl2Alg e)

toX100File :: FilePath -> AlgPlan X100Algebra Plan -> IO ()
toX100File f (m, r, t) = do
    planToFile f (t, rootNodes r, reverseAlgMap m)
  where
      rootNodes :: Plan -> [AlgNode]
      rootNodes (TupleVector qs) = concat $ map rootNodes qs
      rootNodes (DescrVector n) = [n]
      rootNodes (ValueVector n) = [n]
      rootNodes (PrimVal n) = [n]
      rootNodes (NestedVector n q) = n : (rootNodes q)
      rootNodes (PropVector _ ) = error "Prop vectors should only be used internally and never appear in a result"
      rootNodes (Closure _ _ _ _ _) = error "Functions cannot appear as a result value"
      rootNodes (AClosure _ _ _ _ _ _ _) = error "Function cannot appear as a result value"

toX100String :: AlgPlan X100Algebra Plan -> Query X100
toX100String (m, r, t) = 
    let m' = reverseAlgMap m 
    in
        case r of
            PrimVal r'     -> PrimVal $ X100 r' $ generateDumbQuery m' r'
            TupleVector rs -> TupleVector $ map (\r' -> toX100String (m, r', t)) rs
            DescrVector r' -> DescrVector $ X100 r' $ generateDumbQuery m' r' 
            ValueVector r' -> ValueVector $ X100 r' $ generateDumbQuery m' r'
            NestedVector r' rs -> NestedVector (X100 r' $ generateDumbQuery m' r') $ toX100String (m, rs, t)
            PropVector _ -> error "Prop vectors should only be used internally and never appear in a result"
            Closure _ _ _ _ _ -> error "Functions cannot appear as a result value"
            AClosure _ _ _ _ _ _ _ -> error "Function cannot appear as a result value"

toXML :: AlgPlan PFAlgebra Plan -> Query XML
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
    


