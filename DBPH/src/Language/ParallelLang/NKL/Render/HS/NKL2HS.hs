module Language.ParallelLang.NKL.Render.Hs.NKL2HS (programToHs) where

import qualified Language.ParallelLang.NKL.Data.NKL as N
import qualified Language.ParallelLang.Common.Data.Type as T
import Language.ParallelLang.Common.Data.Op
import qualified Language.ParallelLang.Common.Data.Val as V

import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty

programToHs :: ([N.Expr], N.Expr) -> String
programToHs (_, eb) = prettyPrint $ toHs eb

toHs :: N.Expr -> Exp
toHs (N.App _ e1 es) = appFun (toHs e1) (map toHs es)
toHs (N.Let _ v e1 e2) = letE [(nameBind emptyLoc (name v) (toHs e1))] $ toHs e2
toHs (N.If _ e1 e2 e3) = If (toHs e1) (toHs e2) (toHs e3)
toHs (N.BinOp _ (Op n 0) e1 e2) = infixApp (toHs e1) (op $ sym n) (toHs e2)
toHs (N.Const _ v) = valToHs v
toHs (N.Var _ n 0) = var $ name n
toHs (N.Iter _ v e1 e2) = ListComp (toHs e2) [QualStmt $ Generator emptyLoc (pvar $ name v) (toHs e1)]
toHs (N.Nil _) = List []
toHs (N.Proj _ 0 e1 i) = let size = length $ T.tupleComponents $ T.typeOf e1
                             proj = Lambda emptyLoc [PTuple [PVar $ name $ "__pv" ++ show l | l <- [1..size]]] $ var $ name $ "__pv" ++ show i
                          in app proj (toHs e1)
toHs _ = error "toHs not complete"

valToHs :: V.Val -> Exp
valToHs (V.Unit)   = Con $ Special UnitCon
valToHs (V.Int i)  = intE $ toInteger i
valToHs (V.String s) = strE s
valToHs (V.Double d) = (Lit . PrimDouble . toRational) d
valToHs (V.Bool b) = Con $ UnQual $ name $ show b


emptyLoc :: SrcLoc 
emptyLoc = SrcLoc "" 0 0