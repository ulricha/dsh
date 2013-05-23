{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Flattening.NKL.Opt where
       
import           Debug.Trace
import           Text.Printf


import qualified Data.Set as S

import qualified Database.DSH.Flattening.NKL.Data.NKL as NKL
import           Database.DSH.Flattening.NKL.Quote
import           Database.DSH.Impossible
       
-- Perform simple optimizations on the NKL
opt' :: ExprQ -> ExprQ
opt' expr = 
  case expr of 
    tab@(Table _ _ _ _) -> tab
    App t e1 e2 -> App t (opt' e1) (opt' e2)


    -- concatMap pattern: concat $ map (\x -> body) xs
    [nkl|(concat::_ (map::_ (\'v1 -> 'body)::('a -> 'b) 'xs)::_)::'t|] ->

      -- We first test wether the mapped-over list matches a certain pattern:
      -- if p [()] []
      case opt' xs of
        -- In that case, the following rewrite applies
        -- concat $ map (\x -> e) (if p then [()] else [])
        -- => if p then [e] else []
        -- Additionally, we need to check that body does not refer to v1, since we
        -- move it out of that scope.
        [nkl|(if 'p then [unit]::_ else []::_)::_|] | not $ (varName v1) `S.member` (freeVars body) -> 
          
          trace "r1" $ opt' $ [nkl|(if 'p then 'body' else []::'t)::'t|]
          where body' = opt' body

        -- Try to do smart things depending on what is mapped over the list
        xsOpt ->
            case opt' body of
              -- Singleton list construction cancelled out by concat:
              -- concatPrim2 Map (\x -> [e]) xs 
              -- => map (\x -> e) xs
              [nkl|('se : []::_)::_ |] ->

                trace "r2" $ opt' $ [nkl|(map::'mapTy' (\'v1 -> 'se')::'lamTy 'xsOpt)::'t|]

                where se'    = opt' se
                      b'     = elemT b
                      lamTy  = [ty|('a -> 'b')|]
                      mapTy' = [ty|('lamTy -> (['a] -> ['b]))|]
                      
              -- Pull the projection part from a nested comprehension:
              -- concat $ map (\x1 -> map (\x2 -> e) ys) xs
              -- => map (\x1 -> e[x1/fst x1][x2/snd x1]) $ concat $ map (\x1 -> map (\x2 -> (x1, x2)) ys) xs
              [nkl|(map::_ (\'v2 -> 'e)::('c -> _) 'ys)::_|] | noPair v1 v2 e ->

                trace "r3" $ opt' $ 
                [nkl|(map::'prt (\'v1 -> 'projExpr)::'plt
                             (concat::'cot (map::'mt1 (\'v1 -> (map::'mt2 (\'v2 -> 'pairExpr)::'lt2
                                                                          'ys)::['pt])::'lt1
                                                      'xsOpt)::[['pt]])::['pt])::'t|]
                          
                where projExpr = tuplify (v1, a) (v2, c) e
                      pairExpr = [nkl|(pair::('a -> ('c -> 'pt)) 'v1::'a 'v2::'c)::'pt|]

                      -- The type of pairs (a, c)
                      pt       = [ty|('a, 'c)|]
                      -- The result type of the projection expression
                      rt       = elemT t
                      -- The type of the inner lambda
                      lt2      = [ty|('c -> 'pt)|]
                      -- The type of the inner map
                      mt2      = [ty|('lt2 -> (['c] -> ['pt]))|]
                      -- The type of the outer lambda
                      lt1      = [ty|('a -> ['pt])|]
                      -- The type of the outer map
                      mt1      = [ty|('lt1 -> (['a] -> [['pt]]))|]
                      -- The type of concat
                      cot     = [ty|([['pt]] -> ['pt])|]
                      -- The type of the projection lambda
                      plt     = [ty|('pt -> 'rt)|]
                      -- The type of the projection map
                      prt     = [ty|('plt -> (['pt] -> 't))|]
                
              
              -- Pull a filter from a nested comprehension
              -- concat $ map (\x1 -> map (\x2 -> (x1, x2)) (filter (\x2 -> p) ys) xs
              -- => filter (\x1 -> p[x1/fst x1][x2/snd x1]) $ concat $ map (\x1 -> map (\x2 -> (x1, x2)) ys) xs
              [nkl|(map::_ (\'v2 -> (pair::_ 'v3::'t1 'v4::'t2)::_)::_
                           (filter::_ (\'v5 -> 'predE)::_ 'ys)::_)::_|]
                | v1 == v3
                  && v2 == v4
                  && v5 == v2 ->
                  
                trace "r4" $ opt' $ 
                [nkl|(filter::'ft (\'v1 -> 'pairPred)::'flt
                                  (concat::'cot (map::'mt1 (\'v1 -> (map::'mt2 (\'v2 -> (pair::'mkpt 'v1::'t1 'v2::'t2)::'pt)::'lt2
                                                                               'ys)::'pt)::'lt1
                                                           'xsOpt)::['t])::'t)::'t|]
                
                where pairPred = tuplify (v1, t1) (v2, t2) predE
                      -- The type of the pair constructor
                      mkpt     = [ty|('t1 -> ('t2 -> 'pt))|]
                      -- The type of the result pair
                      pt       = [ty|('t1, 't2)|]
                      -- The type of the inner lambda
                      lt2      = [ty|('t2 -> 'pt)|]
                      -- The type of the inner map
                      mt2      = [ty|('lt2 -> (['t2] -> 't))|]
                      -- The type of the outer lambda
                      lt1      = [ty|('t1 -> 't)|]
                      -- The type of the outer map
                      mt1      = [ty|('lt1 -> (['t1] -> ['t]))|]
                      -- The type of concat
                      cot     = [ty|(['t] -> 't)|]
                      -- The type of the filter lambda
                      flt     = [ty|('pt -> bool)|]
                      -- The type of the filter
                      ft      = [ty|('flt -> ('t -> 't))|]
              
              -- Turn a nested iteration into a cartesian product.
              -- concat $ map (\x1 -> map (\x2 -> (x1, x2)) ys) xs
              -- => (x1 × x2)
              -- provided that x1, x2 do not occur free in ys!
              [nkl|(map::_ (\'v2 -> (pair::_ 'v3::'t1 'v4::'t2)::_)::_ 'ys)::_|] 
                | v1 == v3 
                  && v2 == v4 
                  && let fvs = freeVars ys
                     in not ((varName v1) `S.member` fvs)
                        && not ((varName v2) `S.member` fvs) ->

                trace "r5" $ opt' [nkl|(cartProduct::('t1 -> ('t2 -> ('t1, 't2))) 'xsOpt 'ys)::t|]
              
              -- Simple filter pattern:
              -- concat (map  (\x -> if p [x] []) xs)
              -- => filter (\x -> p) xs
              [nkl|(if 'p then ('v2::_ : []::_)::_ else []::_)::_|] | v1 == v2 ->

                trace "r6" $ opt' [nkl|(filter::'filterTy (\'v1 -> 'p)::('a -> bool) 'xsOpt)::t|]

                where filterTy = [ty|(('a -> bool) -> (['a] -> ['a]))|]

              -- More general filter pattern:
              -- concat (map (\x -> if p [e] []) xs)
              -- => map (\x -> e) (filter (\x -> p) xs)
              [nkl|(if 'predE then ('projE : []::_)::_ else []::_)::_|] ->
                
                trace "r7" $ opt' [nkl|(map::'mt (\'v1 -> 'projE)::'pt (filter::'ft (\'v1 -> 'predE)::'ct 'xsOpt)::['a])::'t|]
                
                where c  = elemT t

                      pt = [ty|('a -> 'c)|]
                      mt = [ty|('pt -> (['a] -> ['c]))|]

                      ct = [ty|('a -> bool)|]
                      ft = [ty|(ct -> (['a] -> ['a]))|]


              body' -> 
                  -- We could not do anything smart
                  trace "concatMap def" $ [nkl|(concat::'ct (map::'mt (\'v1 -> 'body')::'pt 'xsOpt)::['t])::'t|]

                  where ct = [ty|(['t] -> 't)|]
                        pt = [ty|('a -> 't)|]
                        mt = [ty|('pt -> (['a] -> ['t]))|]
                 
    AppE1 t p1 e1 -> AppE1 t p1 (opt' e1)
    -- Eliminate pair construction/deconstruction pairs
    -- (fst x, snd x)
    -- => x
    -- [nkl|(pair::(t1 -> (t1 -> (t1, t2))) ('e1)::_ ('e2)::_)::(t1, t2)|] -> 

    -- Eliminate (lifted) identity
    -- map (\x -> x) xs
    -- => xs
    [nkl|(map::_ (\'v1 -> 'v2::_)::_ 'xs)::_|] | v1 == v2 -> trace "r8" $ opt' xs
    
    AppE2 t p1 e1 e2 -> AppE2 t p1 (opt' e1) (opt' e2)
    BinOp t op e1 e2 -> BinOp t op (opt' e1) (opt' e2)
    Lam t v e1 -> Lam t v (opt' e1)
  
    -- Merge nested conditionals:
    -- if c1 (if c2 t []) []
    -- => if c1 && c2 t []
    [nkl|(if 'c1 then (if 'c2 then 'te else []::_)::_ else []::_)::'t|] ->
    
      trace "r9" $ opt' [nkl|(if ('c1 && 'c2)::bool then 'te else []::'t)::'t|]

    If t ce te ee -> If t (opt' ce) (opt' te) (opt' ee)
    constant@(Const _ _) -> constant
    var@(Var _ _) -> var
    AntiE _ -> $impossible
    
-- Substitution: subst v r e ~ e[v/r]
subst :: Var -> ExprQ -> ExprQ -> ExprQ
subst _ _ table@(Table _ _ _ _) = table
subst v r (App t e1 e2)         = App t (subst v r e1) (subst v r e2)
subst v r (AppE1 t p e)         = AppE1 t p (subst v r e)
subst v r (AppE2 t p e1 e2)     = AppE2 t p (subst v r e1) (subst v r e2)
subst v r (BinOp t o e1 e2)     = BinOp t o (subst v r e1) (subst v r e2)
-- FIXME for the moment, we assume that all lambda variables are unique
-- and we don't need to check for name capturing/do alpha-conversion.
subst v r lam@(Lam t v' e)     = if v' == v
                                 then lam
                                 else Lam t v' (subst v r e)
subst _ _ c@(Const _ _)        = c
subst v r var@(Var _ v')       = if v == v' then r else var
subst v r (If t c thenE elseE) = If t (subst v r c) (subst v r thenE) (subst v r elseE)
subst _ _ (AntiE _)            = $impossible

-- tuplify v1 v2 e = e[v1/fst v1][v2/snd v1]
tuplify :: (Var, TypeQ) -> (Var, TypeQ) -> ExprQ -> ExprQ
tuplify (v1, t1) (v2, t2) e = subst v2 v2Rep $ subst v1 v1Rep e

  where v1'    = Var pt v1
        pt     = [ty|('t1, 't2)|]
        v1Rep  = [nkl|(fst::('pt -> 't1) 'v1')::'t1|]
        v2Rep  = [nkl|(snd::('pt -> 't2) 'v1')::'t2|]
  
noPair :: Var -> Var -> ExprQ -> Bool
noPair v1 v2 [nkl|(pair::_ 'v3::_ 'v4::_)::_|] | v1 == v3 && v2 == v4 = False
noPair _  _  _                                                        = True
                       
opt :: NKL.Expr -> NKL.Expr
opt e = if (e /= e') 
        then trace (printf "%s\n---->\n%s" (show e) (show e')) e'
        else trace (show e) e'
  where e' = fromExprQ $ opt' $ toExprQ e
