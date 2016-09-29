module Database.DSH.VSL.Construct where

import qualified Data.List.NonEmpty             as N

import           Database.Algebra.Dag.Build     (Build)
import qualified Database.Algebra.Dag.Build     as B
import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang       as L
import qualified Database.DSH.Common.Type       as Ty
import           Database.DSH.Common.Vector
import           Database.DSH.Common.VectorLang

import           Database.DSH.VSL.Lang          (VSL)
import qualified Database.DSH.VSL.Lang          as VSL

type VSLBuild = Build VSL

class VecNode a where
    inject :: AlgNode -> a
    extract :: a -> AlgNode

instance VecNode DVec where
    inject = DVec
    extract (DVec n) = n

instance VecNode RVec where
    inject = RVec
    extract (RVec n) = n

insertVirtOp :: VSL -> VSLBuild AlgNode
insertVirtOp = B.insert

bindOp :: VecNode a => VSL -> VSLBuild a
bindOp op = inject <$> insertVirtOp op

bindOp2 :: (VecNode a, VecNode b) => VSL -> VSLBuild (a, b)
bindOp2 op = do
    opNode <- insertVirtOp op
    r1Node <- inject <$> (insertVirtOp $ UnOp VSL.R1 opNode)
    r2Node <- inject <$> (insertVirtOp $ UnOp VSL.R2 opNode)
    return (r1Node, r2Node)

bindOp3 :: (VecNode a, VecNode b, VecNode c) => VSL -> VSLBuild (a, b, c)
bindOp3 op = do
    opNode <- insertVirtOp op
    r1Node <- inject <$> (insertVirtOp $ UnOp VSL.R1 opNode)
    r2Node <- inject <$> (insertVirtOp $ UnOp VSL.R2 opNode)
    r3Node <- inject <$> (insertVirtOp $ UnOp VSL.R3 opNode)
    return (r1Node, r2Node, r3Node)

--------------------------------------------------------------------------------

distinct :: DVec -> VSLBuild DVec
distinct dv = bindOp $ UnOp VSL.Distinct (extract dv)

number :: DVec -> VSLBuild DVec
number dv = bindOp $ UnOp VSL.Number (extract dv)

group :: [Expr] -> DVec -> VSLBuild (DVec, DVec, RVec)
group groupExprs dv = bindOp3 $ UnOp (VSL.Group groupExprs) (extract dv)

sort :: [Expr] -> DVec -> VSLBuild (DVec, RVec)
sort sortExprs dv = bindOp2 $ UnOp (VSL.Sort sortExprs) (extract dv)

reverse :: DVec -> VSLBuild (DVec, RVec)
reverse dv = bindOp2 $ UnOp VSL.Reverse (extract dv)

aggrseg :: AggrFun -> DVec -> VSLBuild DVec
aggrseg aFun v = bindOp $ UnOp (VSL.Fold aFun) (extract v)

unboxsng :: DVec -> DVec -> VSLBuild (DVec, RVec)
unboxsng dvo dvi = bindOp2 $ BinOp VSL.UnboxSng (extract dvo) (extract dvi)

unboxdefault :: N.NonEmpty L.ScalarVal -> DVec -> DVec -> VSLBuild (DVec, RVec)
unboxdefault defaultVals vo vi = bindOp2 $ BinOp (VSL.UnboxDefault defaultVals) (extract vo) (extract vi)

append :: DVec -> DVec -> VSLBuild (DVec, RVec, RVec)
append dv1 dv2 = bindOp3 $ BinOp VSL.Append (extract dv1) (extract dv2)

segment :: DVec -> VSLBuild DVec
segment dv = bindOp $ UnOp VSL.Segment (extract dv)

mergemap :: DVec -> VSLBuild RVec
mergemap v = bindOp $ UnOp VSL.MergeMap (extract v)

unsegment :: DVec -> VSLBuild DVec
unsegment dv = bindOp $ UnOp VSL.Unsegment (extract dv)

combine :: DVec -> DVec -> DVec -> VSLBuild (DVec, RVec, RVec)
combine dv1 dv2 dv3 = bindOp3 $ TerOp VSL.Combine (extract dv1) (extract dv2) (extract dv3)

lit :: ([Ty.ScalarType], SegFrame, Segments) -> VSLBuild DVec
lit i = bindOp $ NullaryOp $ VSL.Lit i

tableref :: String -> L.BaseTableSchema -> VSLBuild DVec
tableref n schema = bindOp $ NullaryOp $ VSL.TableRef (n, schema)

project :: [Expr] -> DVec -> VSLBuild DVec
project es dv = bindOp $ UnOp (VSL.Project es) (extract dv)

select :: Expr -> DVec -> VSLBuild (DVec, RVec)
select p dv = bindOp2 $ UnOp (VSL.Select p) (extract dv)

align :: DVec -> DVec -> VSLBuild DVec
align dv1 dv2 = bindOp $ BinOp VSL.Align (extract dv1) (extract dv2)

zip :: DVec -> DVec -> VSLBuild (DVec, RVec, RVec)
zip dv1 dv2 = bindOp3 $ BinOp VSL.Zip (extract dv1) (extract dv2)

cartproduct :: DVec -> DVec -> VSLBuild (DVec, RVec, RVec)
cartproduct dv1 dv2 = bindOp3 $ BinOp VSL.CartProduct (extract dv1) (extract dv2)

replicatescalar :: DVec -> DVec -> VSLBuild (DVec, RVec)
replicatescalar v1 v2 = bindOp2 $ BinOp VSL.ReplicateScalar (extract v1) (extract v2)

replicateseg :: DVec -> DVec -> VSLBuild (DVec, RVec)
replicateseg v1 v2 = bindOp2 $ BinOp VSL.ReplicateSeg (extract v1) (extract v2)

updatemap :: RVec -> RVec -> VSLBuild RVec
updatemap m1 m2 = bindOp $ BinOp VSL.UpdateMap (extract m1) (extract m2)

unitmap :: DVec -> VSLBuild RVec
unitmap m = bindOp $ UnOp VSL.UnitMap (extract m)

updateunit :: RVec -> VSLBuild RVec
updateunit m = bindOp $ UnOp VSL.UpdateUnit (extract m)

materialize :: RVec -> DVec -> VSLBuild (DVec, RVec)
materialize r v = bindOp2 $ BinOp VSL.Materialize (extract r) (extract v)

nestjoinMM :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> VSLBuild (DVec, RVec, RVec)
nestjoinMM p v1 v2 = bindOp3 $ BinOp (VSL.NestJoin (VSL.Direct, VSL.Direct, p')) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

nestjoinMU :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> VSLBuild (DVec, RVec, RVec)
nestjoinMU p v1 v2 = bindOp3 $ BinOp (VSL.NestJoin (VSL.Direct, VSL.Unit, p')) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

thetajoinMM :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> VSLBuild (DVec, RVec, RVec)
thetajoinMM p v1 v2 = bindOp3 $ BinOp (VSL.ThetaJoin (VSL.Direct, VSL.Direct, p')) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

thetajoinMU :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> VSLBuild (DVec, RVec, RVec)
thetajoinMU p v1 v2 = bindOp3 $ BinOp (VSL.ThetaJoin (VSL.Direct, VSL.Unit, p')) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

thetajoinUM :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> VSLBuild (DVec, RVec, RVec)
thetajoinUM p v1 v2 = bindOp3 $ BinOp (VSL.ThetaJoin (VSL.Unit, VSL.Direct, p')) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

groupjoinMM :: L.JoinPredicate L.ScalarExpr -> L.NE AggrFun -> DVec -> DVec -> VSLBuild DVec
groupjoinMM p as v1 v2 = bindOp $ BinOp (VSL.GroupJoin (VSL.Direct, VSL.Direct, p', as)) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

groupjoinMU :: L.JoinPredicate L.ScalarExpr -> L.NE AggrFun -> DVec -> DVec -> VSLBuild DVec
groupjoinMU p as v1 v2 = bindOp $ BinOp (VSL.GroupJoin (VSL.Direct, VSL.Unit, p', as)) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

groupjoinUM :: L.JoinPredicate L.ScalarExpr -> L.NE AggrFun -> DVec -> DVec -> VSLBuild DVec
groupjoinUM p as v1 v2 = bindOp $ BinOp (VSL.GroupJoin (VSL.Unit, VSL.Direct, p', as)) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

antijoinMM :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> VSLBuild (DVec, RVec)
antijoinMM p v1 v2 = bindOp2 $ BinOp (VSL.AntiJoin (VSL.Direct, VSL.Direct, p')) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

antijoinMU :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> VSLBuild (DVec, RVec)
antijoinMU p v1 v2 = bindOp2 $ BinOp (VSL.AntiJoin (VSL.Direct, VSL.Unit, p')) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

antijoinUM :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> VSLBuild (DVec, RVec)
antijoinUM p v1 v2 = bindOp2 $ BinOp (VSL.AntiJoin (VSL.Unit, VSL.Direct, p')) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

semijoinMM :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> VSLBuild (DVec, RVec)
semijoinMM p v1 v2 = bindOp2 $ BinOp (VSL.SemiJoin (VSL.Direct, VSL.Direct, p')) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

semijoinMU :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> VSLBuild (DVec, RVec)
semijoinMU p v1 v2 = bindOp2 $ BinOp (VSL.SemiJoin (VSL.Direct, VSL.Unit, p')) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p

semijoinUM :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> VSLBuild (DVec, RVec)
semijoinUM p v1 v2 = bindOp2 $ BinOp (VSL.SemiJoin (VSL.Unit, VSL.Direct, p')) (extract v1) (extract v2)
  where
    p' = toSLJoinPred p
