{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.Translate.Vec2Algebra (toPFAlgebra, toXML) where

-- FIXME this should import a module from TableAlgebra which defines 
-- common types like schema info and abstract column types.
import Database.Algebra.Pathfinder(natT, PFAlgebra)

import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.VL.PathfinderVectorPrimitives
import Language.ParallelLang.Common.Data.Val
import Database.Algebra.Graph.GraphBuilder
import Language.ParallelLang.FKL.Data.FKL
import qualified Language.ParallelLang.VL.Data.VectorTypes as T
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.VL.Data.Query
import Database.Algebra.Pathfinder.Render.XML hiding (XML, Graph)
import qualified Language.ParallelLang.Common.Data.Type as Ty
import Language.ParallelLang.VL.VectorOperations

import qualified Data.Map as M
import Control.Applicative hiding (Const)
import Control.Monad (liftM2)

import Language.ParallelLang.Common.Impossible

fkl2Alg :: (VectorAlgebra a) => Expr Ty.Type -> Graph a Plan
fkl2Alg (Tuple _ es) = TupleVector <$> mapM fkl2Alg es
fkl2Alg (Table _ n cs ks) = tableRef n cs ks
fkl2Alg (Labeled _ e) = fkl2Alg e
fkl2Alg (Const t v) = constructLiteral t v 
fkl2Alg (Nil (Ty.List t@(Ty.List _))) = do
  p <- fkl2Alg (Nil t)
  p_empty <- emptyVector [(descr, natT), (pos, natT)]
  return (NestedVector p_empty p)
fkl2Alg (Nil (Ty.List t)) = do
  p_empty <- emptyVector [(descr, natT), (pos, natT), (item1, convertType t)]
  return (ValueVector p_empty)
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
                                                binOp l o p1 p2
fkl2Alg (Proj _ _ e n) = do
                          (TupleVector es) <- fkl2Alg e
                          return $ es !! (n - 1)
fkl2Alg (If t eb e1 e2) = do
                             pc <- fkl2Alg eb
                             pt <- fkl2Alg e1
                             pe <- fkl2Alg e2
                             case Ty.listDepth t of
                               0 -> ifPrimValues pc pt pe
                               1 -> ifValueVectors pc pt pe
                               _ -> error "vec2Alg: Can't translate if construction"
  
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

-- FIXME
-- undefined is used here because the flattening code generation does not use 
-- loop relations. At some point, loop should be separated from the general
-- GraphM monad.                              
toPFAlgebra :: Expr Ty.Type -> AlgPlan PFAlgebra Plan
toPFAlgebra e = runGraph undefined (fkl2Alg e)

--toX100Algebra :: Expr Ty.Type -> AlgPlan X100Algebra Plan
--toX100Algebra e = runGraph initialLoop (fkl2Alg e)

-- toX100Algebra :: Expr Ty.Type -> AlgPlan X100Algebra Plan
-- toX100Algebra e = runGraph initLoop (fkl2Alg e)

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
    


