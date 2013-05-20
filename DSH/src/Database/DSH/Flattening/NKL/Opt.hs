module Database.DSH.Flattening.NKL.Opt where
       
import Debug.Trace
import Text.Printf

import Database.DSH.Flattening.NKL.Data.NKL
import Database.DSH.Flattening.Common.Data.Val
import Database.DSH.Flattening.Common.Data.Op
-- FIXME rename Type data constructors in Common.Data.Type to get rid of naming
-- conflicts
import Database.DSH.Flattening.Common.Data.Type hiding(Var, List, Unit, Pair)
import qualified Database.DSH.Flattening.Common.Data.Type as T


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
                         
              -- Merge nested loops by introducing a cartesian product:
              -- concat $ map (\x -> map (\y -> e) ys) xs
              -- => map (\(x, y) -> e) (xs × ys)
              -- 
              -- Actually, since we can't match on lambda arguments and there
              -- is no let-binding, we rewrite the lambda into the following:
              -- (\x -> e[x/fst x][y/snd x])
              -- 
              -- Note that we re-use x to avoid the need for fresh variables,
              -- which is fine here.
              AppE2 _ (Map _) (Lam (Fn elemTy2 resTy2) innerVar innerBody) ys ->
                let productType = T.Pair elemTy elemTy2

                    tupleComponent :: (Type -> Prim1) -> Type -> Expr
                    tupleComponent f ty = (AppE1 ty (f (productType .-> ty)) (Var productType var))

                    innerBody' = subst innerVar 
                                       (tupleComponent Snd elemTy2) 
                                       (subst var (tupleComponent Fst elemTy) innerBody)

                    ys'        = opt' ys

                in AppE2 t 
                         (Map ((productType .-> resTy2) .-> (listT productType .-> listT resTy2)))
                         (Lam (productType .-> resTy2) var innerBody')
                         (AppE2 (listT productType) 
                                (CartProduct (listT elemTy .-> (listT elemTy2 .-> (listT productType)))) 
                                             xs' 
                                             ys')

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

      trace ("r5 " ++ (show e)) $ opt' $ If t1 
                (BinOp boolT Conj c1 c2)
                t
                (Const t1 (List []))
           
    If t ce te ee -> If t (opt' ce) (opt' te) (opt' ee)
    constant@(Const _ _) -> constant
    var@(Var _ _) -> var
    
-- Substitution: subst v r e ~ e[v/r]
subst :: String -> Expr -> Expr -> Expr
subst _ _ t@(Table _ _ _ _) = t
subst v r (App t e1 e2)     = App t (subst v r e1) (subst v r e2)
subst v r (AppE1 t p e)     = AppE1 t p (subst v r e)
subst v r (AppE2 t p e1 e2) = AppE2 t p (subst v r e1) (subst v r e2)
subst v r (BinOp t o e1 e2) = BinOp t o (subst v r e1) (subst v r e2)
-- FIXME for the moment, we assume that all lambda variables are unique
-- and we don't need to check for name capturing/do alpha-conversion.
subst v r lam@(Lam t v' e)  = if v == v' 
                              then lam
                              else Lam t v' (subst v r e)
subst _ _ c@(Const _ _)     = c
subst v r var@(Var _ v')    = if v == v' then r else var
subst v r (If ty c t e)     = If ty (subst v r c) (subst v r t) (subst v r e)

opt :: Expr -> Expr
opt e = if (e /= e') 
        then trace (printf "%s\n---->\n%s" (show e) (show e')) e'
        else trace (show e) e'
  where e' = opt' e
