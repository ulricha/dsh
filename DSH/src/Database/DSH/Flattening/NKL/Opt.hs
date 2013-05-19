module Database.DSH.Flattening.NKL.Opt where
       
import Debug.Trace
import Text.Printf

import Database.DSH.Flattening.NKL.Data.NKL
import Database.DSH.Flattening.Common.Data.Val
import Database.DSH.Flattening.Common.Data.Op
import Database.DSH.Flattening.Common.Data.Type hiding(Var, List, Unit)

-- Perform simple optimizations on the NKL
opt' :: Expr -> Expr
opt' e =
  case e of 
    tab@(Table _ _ _ _) -> tab
    App t e1 e2 -> App t (opt' e1) (opt' e2)

    -- concatMap pattern: concat $ map (\x -> body) xs
    AppE1 t
          (Concat concatTy)
          (AppE2 innerTy
                 (Map mapTy) 
                 (Lam (Fn elemTy resTy) var body) xs) ->
      -- Try to do smart things depending on what is mapped over the list
      case opt' body of
        -- Filter pattern: concat (map  (\x -> if e [x] []) xs)
        If _
           -- the filter condition
           c 
           -- then-branch: singleton list
           (BinOp _ Cons (Var _ var') (Const _ (List [])))
           -- else-branch: empty list
           (Const _ (List [])) | var == var' ->

          -- Turns into: filter (\x -> e) xs
          opt' $ AppE2 t
                       (Filter ((elemTy .-> boolT) .-> ((listT elemTy) .-> t)))
                       (Lam (elemTy .-> boolT) var c)
                       (opt' xs)

        body' -> 
          case opt' xs of
            -- if p [x] []
            If _ p (Const _ (List [Unit])) (Const _ (List [])) -> 
              -- Less craziness: if p [x] [] 
              -- FIXME to be really sound here, we need to check wether body'
              -- references var.
              opt' $ If t p body' (Const t (List []))
            -- We could not do anything smart
            xs' -> AppE1 t
                       (Concat concatTy)
                       (AppE2 innerTy
                              (Map mapTy) 
                              (Lam (Fn elemTy resTy) var body') xs')
    AppE1 t p1 e1 -> AppE1 t p1 (opt' e1)
    AppE2 t p1 e1 e2 -> AppE2 t p1 (opt' e1) (opt' e2)
    BinOp t op e1 e2 -> BinOp t op (opt' e1) (opt' e2)
    Lam t v e1 -> Lam t v (opt' e1)
  
    -- Merge nested conditionals:
    -- if c1 (if c2 t []) []
    -- -> if c1 && c2 t []
    If t1
       c1
       (If _
           c2
           t
           (Const _ (List [])))
       (Const _ (List [])) ->

      opt' $ If t1 
                (BinOp boolT Conj c1 c2)
                t
                (Const t1 (List []))
           
    If t ce te ee -> If t (opt' ce) (opt' te) (opt' ee)
    constant@(Const _ _) -> constant
    var@(Var _ _) -> var

opt :: Expr -> Expr
opt e = if (e /= e') 
        then trace (printf "%s\n---->\n%s" (show e) (show e')) e'
        else trace (show e) e'
  where e' = opt' e
