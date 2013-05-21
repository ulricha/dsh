module Database.DSH.Flattening.NKL.Opt where
       
import Debug.Trace
import Text.Printf

import Database.DSH.Flattening.NKL.Data.NKL
import Database.DSH.Flattening.Common.Data.Val
import Database.DSH.Flattening.Common.Data.Op
import Database.DSH.Flattening.Common.Data.Type

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
                 (Lam (FunT elemTy resTy) var body) xs) ->
      -- We first test wether the mapped-over list matches a certain pattern:
      -- if p [()] []
      case opt' xs of
        -- In that case, the following rewrite applies
        -- concat $ map (\x -> e) (if p then [()] else [])
        -- => if p then [e] else []
        -- FIXME to be really sound here, we need to check wether body'
        -- references var.
        If _ p (Const _ (List [Unit])) (Const _ (List [])) -> 
          trace ("r1 " ++ (show e)) $ opt' $ If t p (opt' body) (Const t (List []))

        -- Try to do smart things depending on what is mapped over the list
        xs' ->
            case opt' body of
              BinOp _ Cons singletonExpr (Const _ (List [])) ->
                -- Singleton list construction cancelled out by concat:
                -- concatMap (\x -> [e]) xs => map (\x -> e) xs
                trace ("r2 " ++ (show e)) $ opt' $ AppE2 t 
                         -- FIXME typeOf is potentially dangerous since the type
                         -- language includes variables.
                         (Map ((elemTy .-> (typeOf body)) .-> ((listT elemTy) .-> t)))
                         (Lam (elemTy .-> (typeOf body))
                              var
                              singletonExpr)
                         (opt' xs)

              -- Filter pattern: concat (map  (\x -> if p [x] []) xs)
              If _
                 -- the filter condition
                 p 
                 -- then-branch: singleton list
                 (BinOp _ Cons (Var _ var') (Const _ (List [])))
                 -- else-branch: empty list
                 (Const _ (List [])) | var == var' ->

                -- Turns into: filter (\x -> e) xs
                trace ("r3 " ++ (show e)) $ opt' $ AppE2 t
                             (Filter ((elemTy .-> boolT) .-> ((listT elemTy) .-> t)))
                             (Lam (elemTy .-> boolT) var p)
                             (opt' xs)

              -- More general filter pattern:
              -- concat (map (\x -> if p [e] []) xs)
              -- => map (\x -> e) (filter (\x -> p) xs)
              If _
                 -- the filter condition
                 p 
                 -- then-branch: singleton list over an arbitrary expression
                 (BinOp _ Cons bodyExpr (Const _ (List [])))
                 -- else-branch: empty list
                 (Const _ (List [])) ->

                trace ("r4 " ++ (show e)) $ opt' $ AppE2 t
                             (Map ((elemTy .-> (elemT resTy)) .-> ((listT elemTy) .-> t)))
                             (Lam (elemTy .-> (elemT resTy)) var bodyExpr)
                             (AppE2 t
                                    (Filter ((elemTy .-> boolT) .-> ((listT elemTy) .-> t)))
                                    (Lam (elemTy .-> boolT) var p)
                                    (opt' xs))

              body' -> 
                  -- We could not do anything smart
                  AppE1 t
                        (Concat concatTy)
                        (AppE2 innerTy
                               (Map mapTy) 
                               (Lam (FunT elemTy resTy) var body') xs')
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

      trace ("r5 " ++ (show e)) $ opt' $ If t1 
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
