{-# LANGUAGE ConstraintKinds #-}

module Database.DSH.VSL.Construct where

import qualified Data.List.NonEmpty             as N

import           Database.Algebra.Dag.Build     (Build)
import qualified Database.Algebra.Dag.Build     as B
import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Vector
import           Database.DSH.Common.VectorLang

import           Database.DSH.VSL.Lang          (VSL)
import qualified Database.DSH.VSL.Lang          as VSL

type VSLBuild r e = Build (VSL r e)

class VecNode a where
    inject :: AlgNode -> a
    extract :: a -> AlgNode

instance VecNode DVec where
    inject = DVec
    extract (DVec n) = n

instance VecNode RVec where
    inject = RVec
    extract (RVec n) = n

insertVirtOp :: Ordish r e => VSL r e -> VSLBuild r e AlgNode
insertVirtOp = B.insert

bindOp :: (Ordish r e, VecNode a) => VSL r e -> VSLBuild r e a
bindOp op = inject <$> insertVirtOp op

bindOp2 :: (Ordish r e, VecNode a, VecNode b) => VSL r e -> VSLBuild r e (a, b)
bindOp2 op = do
    opNode <- insertVirtOp op
    r1Node <- inject <$> (insertVirtOp $ UnOp VSL.R1 opNode)
    r2Node <- inject <$> (insertVirtOp $ UnOp VSL.R2 opNode)
    return (r1Node, r2Node)

bindOp3 :: (Ordish r e, VecNode a, VecNode b, VecNode c) => VSL r e -> VSLBuild r e (a, b, c)
bindOp3 op = do
    opNode <- insertVirtOp op
    r1Node <- inject <$> (insertVirtOp $ UnOp VSL.R1 opNode)
    r2Node <- inject <$> (insertVirtOp $ UnOp VSL.R2 opNode)
    r3Node <- inject <$> (insertVirtOp $ UnOp VSL.R3 opNode)
    return (r1Node, r2Node, r3Node)

--------------------------------------------------------------------------------

distinct :: Ordish r e => DVec -> VSLBuild r e DVec
distinct dv = bindOp $ UnOp VSL.Distinct (extract dv)

number :: Ordish r e => DVec -> VSLBuild r e DVec
number dv = bindOp $ UnOp VSL.Number (extract dv)

group :: Ordish r e => r -> DVec -> VSLBuild r e (DVec, DVec, RVec)
group groupExpr dv = bindOp3 $ UnOp (VSL.Group groupExpr) (extract dv)

sort :: Ordish r e => r -> DVec -> VSLBuild r e (DVec, RVec)
sort sortExpr dv = bindOp2 $ UnOp (VSL.Sort sortExpr) (extract dv)

reverse :: Ordish r e => DVec -> VSLBuild r e (DVec, RVec)
reverse dv = bindOp2 $ UnOp VSL.Reverse (extract dv)

aggrseg :: Ordish r e => AggrFun e -> DVec -> VSLBuild r e DVec
aggrseg aFun v = bindOp $ UnOp (VSL.Fold aFun) (extract v)

unboxsng :: Ordish r e => DVec -> DVec -> VSLBuild r e (DVec, RVec)
unboxsng dvo dvi = bindOp2 $ BinOp VSL.UnboxSng (extract dvo) (extract dvi)

unboxdefault :: Ordish r e => N.NonEmpty L.ScalarVal -> DVec -> DVec -> VSLBuild r e (DVec, RVec)
unboxdefault defaultVals vo vi = bindOp2 $ BinOp (VSL.UnboxDefault defaultVals) (extract vo) (extract vi)

append :: Ordish r e => DVec -> DVec -> VSLBuild r e (DVec, RVec, RVec)
append dv1 dv2 = bindOp3 $ BinOp VSL.Append (extract dv1) (extract dv2)

segment :: Ordish r e => DVec -> VSLBuild r e DVec
segment dv = bindOp $ UnOp VSL.Segment (extract dv)

mergemap :: Ordish r e => DVec -> VSLBuild r e RVec
mergemap v = bindOp $ UnOp VSL.MergeMap (extract v)

unsegment :: Ordish r e => DVec -> VSLBuild r e DVec
unsegment dv = bindOp $ UnOp VSL.Unsegment (extract dv)

combine :: Ordish r e => DVec -> DVec -> DVec -> VSLBuild r e (DVec, RVec, RVec)
combine dv1 dv2 dv3 = bindOp3 $ TerOp VSL.Combine (extract dv1) (extract dv2) (extract dv3)

lit :: Ordish r e => (PType, VecSegs) -> VSLBuild r e DVec
lit i = bindOp $ NullaryOp $ VSL.Lit i

tableref :: Ordish r e => String -> L.BaseTableSchema -> VSLBuild r e DVec
tableref n schema = bindOp $ NullaryOp $ VSL.TableRef (n, schema)

project :: Ordish r e => r -> DVec -> VSLBuild r e DVec
project e dv = bindOp $ UnOp (VSL.Project e) (extract dv)

select :: Ordish r e => e -> DVec -> VSLBuild r e (DVec, RVec)
select p dv = bindOp2 $ UnOp (VSL.Select p) (extract dv)

align :: Ordish r e => DVec -> DVec -> VSLBuild r e DVec
align dv1 dv2 = bindOp $ BinOp VSL.Align (extract dv1) (extract dv2)

zip :: Ordish r e => DVec -> DVec -> VSLBuild r e (DVec, RVec, RVec)
zip dv1 dv2 = bindOp3 $ BinOp VSL.Zip (extract dv1) (extract dv2)

cartproduct :: Ordish r e => DVec -> DVec -> VSLBuild r e (DVec, RVec, RVec)
cartproduct dv1 dv2 = bindOp3 $ BinOp VSL.CartProduct (extract dv1) (extract dv2)

replicatescalar :: Ordish r e => DVec -> DVec -> VSLBuild r e (DVec, RVec)
replicatescalar v1 v2 = bindOp2 $ BinOp VSL.ReplicateScalar (extract v1) (extract v2)

replicateseg :: Ordish r e => DVec -> DVec -> VSLBuild r e (DVec, RVec)
replicateseg v1 v2 = bindOp2 $ BinOp VSL.ReplicateSeg (extract v1) (extract v2)

updatemap :: Ordish r e => RVec -> RVec -> VSLBuild r e RVec
updatemap m1 m2 = bindOp $ BinOp VSL.UpdateMap (extract m1) (extract m2)

unitmap :: Ordish r e => DVec -> VSLBuild r e RVec
unitmap m = bindOp $ UnOp VSL.UnitMap (extract m)

updateunit :: Ordish r e => RVec -> VSLBuild r e RVec
updateunit m = bindOp $ UnOp VSL.UpdateUnit (extract m)

materialize :: Ordish r e => RVec -> DVec -> VSLBuild r e (DVec, RVec)
materialize r v = bindOp2 $ BinOp VSL.Materialize (extract r) (extract v)

nestjoinMM :: Ordish r e => L.JoinPredicate e -> DVec -> DVec -> VSLBuild r e (DVec, RVec, RVec)
nestjoinMM p v1 v2 = bindOp3 $ BinOp (VSL.NestJoin (VSL.Direct, VSL.Direct, p)) (extract v1) (extract v2)

nestjoinMU :: Ordish r e => L.JoinPredicate e -> DVec -> DVec -> VSLBuild r e (DVec, RVec, RVec)
nestjoinMU p v1 v2 = bindOp3 $ BinOp (VSL.NestJoin (VSL.Direct, VSL.Unit, p)) (extract v1) (extract v2)

thetajoinMM :: Ordish r e => L.JoinPredicate e -> DVec -> DVec -> VSLBuild r e (DVec, RVec, RVec)
thetajoinMM p v1 v2 = bindOp3 $ BinOp (VSL.ThetaJoin (VSL.Direct, VSL.Direct, p)) (extract v1) (extract v2)

thetajoinMU :: Ordish r e => L.JoinPredicate e -> DVec -> DVec -> VSLBuild r e (DVec, RVec, RVec)
thetajoinMU p v1 v2 = bindOp3 $ BinOp (VSL.ThetaJoin (VSL.Direct, VSL.Unit, p)) (extract v1) (extract v2)

thetajoinUM :: Ordish r e => L.JoinPredicate e -> DVec -> DVec -> VSLBuild r e (DVec, RVec, RVec)
thetajoinUM p v1 v2 = bindOp3 $ BinOp (VSL.ThetaJoin (VSL.Unit, VSL.Direct, p)) (extract v1) (extract v2)

groupjoinMM :: Ordish r e => L.JoinPredicate e -> L.NE (AggrFun e) -> DVec -> DVec -> VSLBuild r e DVec
groupjoinMM p as v1 v2 = bindOp $ BinOp (VSL.GroupJoin (VSL.Direct, VSL.Direct, p, as)) (extract v1) (extract v2)

groupjoinMU :: Ordish r e => L.JoinPredicate e -> L.NE (AggrFun e) -> DVec -> DVec -> VSLBuild r e DVec
groupjoinMU p as v1 v2 = bindOp $ BinOp (VSL.GroupJoin (VSL.Direct, VSL.Unit, p, as)) (extract v1) (extract v2)

groupjoinUM :: Ordish r e => L.JoinPredicate e -> L.NE (AggrFun e) -> DVec -> DVec -> VSLBuild r e DVec
groupjoinUM p as v1 v2 = bindOp $ BinOp (VSL.GroupJoin (VSL.Unit, VSL.Direct, p, as)) (extract v1) (extract v2)

antijoinMM :: Ordish r e => L.JoinPredicate e -> DVec -> DVec -> VSLBuild r e (DVec, RVec)
antijoinMM p v1 v2 = bindOp2 $ BinOp (VSL.AntiJoin (VSL.Direct, VSL.Direct, p)) (extract v1) (extract v2)

antijoinMU :: Ordish r e => L.JoinPredicate e -> DVec -> DVec -> VSLBuild r e (DVec, RVec)
antijoinMU p v1 v2 = bindOp2 $ BinOp (VSL.AntiJoin (VSL.Direct, VSL.Unit, p)) (extract v1) (extract v2)

antijoinUM :: Ordish r e => L.JoinPredicate e -> DVec -> DVec -> VSLBuild r e (DVec, RVec)
antijoinUM p v1 v2 = bindOp2 $ BinOp (VSL.AntiJoin (VSL.Unit, VSL.Direct, p)) (extract v1) (extract v2)

semijoinMM :: Ordish r e => L.JoinPredicate e -> DVec -> DVec -> VSLBuild r e (DVec, RVec)
semijoinMM p v1 v2 = bindOp2 $ BinOp (VSL.SemiJoin (VSL.Direct, VSL.Direct, p)) (extract v1) (extract v2)

semijoinMU :: Ordish r e => L.JoinPredicate e -> DVec -> DVec -> VSLBuild r e (DVec, RVec)
semijoinMU p v1 v2 = bindOp2 $ BinOp (VSL.SemiJoin (VSL.Direct, VSL.Unit, p)) (extract v1) (extract v2)

semijoinUM :: Ordish r e => L.JoinPredicate e -> DVec -> DVec -> VSLBuild r e (DVec, RVec)
semijoinUM p v1 v2 = bindOp2 $ BinOp (VSL.SemiJoin (VSL.Unit, VSL.Direct, p)) (extract v1) (extract v2)
