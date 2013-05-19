module Database.DSH.Flattening.NKL.Opt where
       
import Debug.Trace

import Database.DSH.Flattening.NKL.Data.NKL
import Database.DSH.Flattening.Common.Data.Val
import Database.DSH.Flattening.Common.Data.Op
import Database.DSH.Flattening.Common.Data.Type hiding(Var, List, Unit)

-- Perform simple optimizations on the NKL
opt :: Expr -> Expr
opt e = trace (show e') e'
  where
  e' = 
    case e of 
      tab@(Table _ _ _ _) -> tab
      App t e1 e2 -> App t (opt e1) (opt e2)

      -- concatMap pattern: concat $ map (\x -> body) xs
      AppE1 t
            (Concat concatTy)
            (AppE2 innerTy
                   (Map mapTy) 
                   (Lam (Fn elemTy resTy) var body) xs) ->
        -- Try to do smart things depending on what is mapped over the list
        case opt body of
          -- Filter pattern: concat (map  (\x -> if e [x] []) xs)
          If _
             -- the filter condition
             c 
             -- then-branch: singleton list
             (BinOp _ Cons (Var _ var') (Const _ (List [])))
             -- else-branch: empty list
             (Const _ (List [])) | var == var' ->

            -- Turns into: filter (\x -> e) xs
            AppE2 t
                  (Filter ((elemTy .-> boolT) .-> ((listT elemTy) .-> t)))
                  (Lam (elemTy .-> boolT) var c)
                  xs

          -- Monad comprehension guard craziness:
          -- concat $ map (\_ -> [x]) (if p [()] [])
          body'@(BinOp bodyTy Cons _ (Const _ (List []))) ->
              case xs of
                -- if p [x] []
                If _ p (Const _ (List [Unit])) (Const _ (List [])) -> 
                  -- Less craziness: if p [x] []
                  If t p body (Const bodyTy (List []))
                _ -> 
                  AppE1 t
                        (Concat concatTy)
                        (AppE2 innerTy
                               (Map mapTy) 
                               (Lam (Fn elemTy resTy) var body') xs)
                
          -- We could not do anything smart
          body' -> 
            AppE1 t
                  (Concat concatTy)
                  (AppE2 innerTy
                         (Map mapTy) 
                         (Lam (Fn elemTy resTy) var body') xs)
      AppE1 t p1 e1 -> AppE1 t p1 (opt e1)
      AppE2 t p1 e1 e2 -> AppE2 t p1 (opt e1) (opt e2)
      BinOp t op e1 e2 -> BinOp t op (opt e1) (opt e2)
      Lam t v e1 -> Lam t v (opt e1)
      If t ce te ee -> If t (opt ce) (opt te) (opt ee)
      constant@(Const _ _) -> constant
      var@(Var _ _) -> var

