\newpage
%{
%include fkl.fmt
%include nklQual.fmt
%include setQual.fmt
%include fklQual.fmt
\chapter{The flattening transformation}
In this chapter we describe how the flattening transformation is performed. The flattening transformation has been described in numerous papers \cite{Goldberg24, Palmer95, Prins93} and more recently in the context of Data Parallel Haskell \cite{Keller98, Keller99, Jones08, Leschinskiy06}. The flattening transformation aims to transform arbitrarily nested programs into flat programs, where the notion of nesting is encoded through multiple flat lists. The flattening transformation described in this chapter is extremely similar to the the flattening transformation described in \cite{Jones08}.

%if False
\begin{code}
{-# LANGUAGE TemplateHaskell, TupleSections #-}
module Database.DSH.Flattening.Translate.NKL2FKL (flatten) where

import qualified Database.DSH.Flattening.FKL.Data.FKL as F
import qualified Database.DSH.Flattening.NKL.Data.NKL as N
import Database.DSH.Flattening.Common.TransM

import Database.DSH.Flattening.FKL.FKLPrimitives
import Database.DSH.Flattening.Common.Data.Type

import qualified Data.Set as S

import Control.Applicative
\end{code}
%endif

\section{The goal of flattening}

The goal of the flattening transformation is to make programs more suitable for parallel execution. When we map a function over all elements of a list this is an opportunity for parallelism as the application of the function to each individual element of the list is independent of all the other applications, these applications can thus be executed in parallel.
It is however not easy to execute an arbitrarily nested program in parallel. Ideally we would have every processor perform the same operations at the same time, this is however not easily achievable for arbitrarily nested data in an efficient manner. We can however transform a nested program into a flat program, which we can then execute in parallel.
The flattening transformation eliminates all occurrences of |map|, primitive operations are lifted to their vector equivalents.

\section{Lifting, an intuition}

The lifting transformation eliminates occurrences of |map|, in order to do so it needs to replicate certain values. In this section we will informally describe what happens to values and variables inside (nested-) |map| expressions.

We start out with a trivial case: |map (\x -> x) [10,20,30] |. The flattening transformation replaces maps with functions that process vectors. In our example the type of |x| will change from |Int| in the original expression to |[Int]| in the flattened expression. The value of |x| will change from |10| in the first iteration |20| in the second and |30| in the last in the original expression, into |[10,20,30]| in one application in the flattened expression. The comprehension will thus be translated into: |(\x -> x) [10,20,30]|. All consecutive values for |x| (or any other value/variable) are packed together in one vector and are applied to vector operations.   

Constant values in map expressions are replicated to form constant vectors. Consider for example the following expression: | map (\x -> 10 + x) [10,20, 30]|. This expression is translated into: |(\x -> dist 10 x (level plus 1) x) [10,20,30]|. The constant value |10| is replicated into a vector with a shape that matches the shape of the vector for |x|. 

When maps are nested the values of the inner map have to be replicated as well. Consider for example the following expression: | map (\x -> (map (\y -> y) [10,20,30])) [40,50] |. This expression evaluates to: | [[10,20,30],[10,20,30]] |. The values for |y| in each consecutive step are |[10,20,30,10,20,30]|. And this exactly the vector that should be passed in as value for |y|. The result shows a nested list, this nesting can be reintroduced after finishing the inner computation. We obtain the shape of the result by distributing the inner vector over the outer vector: |dist [10,20,30] [40,50]|. The result of this computation is nested and represented by two vectors |[(1,1),(1,2)]| and |[(1,1,10),(1,2,20),(1,3,30),(2,4,10),(2,5,20),(2,6,30)]|. The first vector is a descriptor vector describing the outer structure. The second vector is a value vector that contains all values. When evaluating the inner context we would want to forget about the nesting, to this end we apply concat to remove the nesting and get only the value vector. We can reintroduce the shape by reattaching the outer descriptor, this is done by the |unconcat| function. This function takes the outer descriptor of a given value and attaches it to another one. So fully desugared we get: |(\x -> unconcat (dist [10,20,30] x) $ (\y -> y) (concat $ dist [10,20,30] x)) [40,50]|. By introducing |concat| and |unconcat| we prevent ourselves from having to generate code for higher lifted functions. 

As a final example let us now consider the following example: |map (\x -> map (\y -> x + y) [10,20,30]) [40,50]|. As before in the flattened version the value for |y| in the inner lambda will be |[10,20,30,10,20,30]| in consecutive iterations and this is again obtained the computation |concat (dist [10,20,30] [40,50])|. The values for |x| in the inner lambda will be |[40,40,40,50,50,50]| in the consecutive iterations. The unflattened version of that vector has to have exactly the same shape as the unflattened version of the vector for |y|. So the shape is determined by |dist [10,20,30] [40,50]|. This gives a nested list where there are two inner lists with each a length of 3 elements. The right values are then obtained by applying the lifted version of |dist| namely |(level dist 1)| and then flattening the result. The vector for |x| is thus constructed by the following expression: |concat $ (level dist 1) [40,50] (dist [10,20,30] [40,50])|. The whole expression is desugared to: 
\begin{spec}
(\x ->  (unconcat $ dist [10,20,30] x) $ 
            (\x y -> x (level plus 1) y) 
                (concat $ (level dist 1) x $ dist [10,20,30] x) 
                (concat $ dist [10,20,30] x)
) [40,50] 
\end{spec}

The strategy provided above for dealing with nested maps and replicating variables also applies to deeper nested comprehensions. In those cases just like with two nested comprehensions we flatten (concat) values when we step into the nested expression, and expand (unconcat) the result of the nested expression. The concat/unconcat pattern is captured in our implementation of map, which is described in the next chapter along with other functions.


\section{Representing functions as first class citizens}

In Haskell functions are treated the same as values are, and can thus be passed to another function as an argument or put in a list. In order to achieve this in DBPH we introduce a new syntactic node, a closure

A closure is build out of three components, a set of variables that occur free in the function body. A flattened version of the lambda and a lifted version. This lifted version is needed to deal with the fact any lambda might be passed to a map function. A closure will be represented as: | Clo env e1 e2 |. A closure has a type | t1 :-> t2 |. Note that the function type constructor is slightly different from the regular function space constructor | -> |. A closure can be distributed like any other primitive type and can thus appear in a list. Technically it is possible to construct a list of several different closures, this however goes against the very nature of the flattening transformation and such lists are never constructed by the flattening transformation. All primitives operations can also be performed on closures.

Distribute over a closure is defined as follows:
\begin{spec}
dist (Clo ((x1, ..., xn)) f f') e = AClo ((e, dist x1 e, ..., dist xn e)) f f'
\end{spec}
The result type is a list of closures: |[t1 :-> t2]|. Distribute over (nested-) lists of closure is defined similarly. Other primitive operations as  |length|, |concat| and |unconcat| are defined similar to |dist|.

It is of course also possible to use a list of closures as second argument to |dist| and distribute over that list. The alert reader might have noticed that in the lifted closure the environment is expanded with an extra value. This extra value represents the iteration context, and is expected as an argument by |f'|, it is the value that is used to distribute values to the right length.

We also introduce a construct for applying a closure to an argument, namely | cloLAppM |. The type of |(cloLAppM)| is: |[t1 :-> t2] -> [t1] -> [t2]|.

The semantics of |cloLAppM| and |cloLAppM|:

\begin{spec}
cloAppM (Clo ((x1, ..., xn)) f f') x == f x1 ... xn x
cloLAppM (AClo ((n, x1, ..., xn)) f f') x == f' n x1 ... xn x
\end{spec}

%if False
\begin{code}
        
flatten :: N.Expr -> F.Expr
flatten e = runTransform (flatTransform e)

flatTransform :: N.Expr -> TransM F.Expr
flatTransform = transform 

prim1Transform :: (N.Prim1 Type) -> F.Expr
prim1Transform (N.Length t) = lengthVal t
prim1Transform (N.Not t) = notVal t
prim1Transform (N.Concat t) = concatVal t
prim1Transform (N.Sum t) = sumVal t
prim1Transform (N.Avg t) = avgVal t
prim1Transform (N.Minimum t) = minimumVal t
prim1Transform (N.Maximum t) = maximumVal t
prim1Transform (N.The t) = theVal t
prim1Transform (N.Head t) = headVal t
prim1Transform (N.Fst t) = fstVal t
prim1Transform (N.Snd t) = sndVal t
prim1Transform (N.IntegerToDouble t) = integerToDoubleVal t
prim1Transform (N.Tail t) = tailVal t
prim1Transform (N.Reverse t) = reverseVal t
prim1Transform (N.And t) = andVal t
prim1Transform (N.Or t) = orVal t
prim1Transform (N.Init t) = initVal t
prim1Transform (N.Last t) = lastVal t
prim1Transform (N.Nub t) = nubVal t

prim2Transform :: (N.Prim2 Type) -> F.Expr
prim2Transform (N.Map t) = mapVal t
prim2Transform (N.SortWith t) = sortWithVal t
prim2Transform (N.GroupWithKey t) = groupWithKeyVal t
prim2Transform (N.Pair t) = pairVal t 
prim2Transform (N.Filter t) = filterVal t 
prim2Transform (N.Append t) = appendVal t
prim2Transform (N.Index t) = indexVal t
prim2Transform (N.Take t) = takeVal t
prim2Transform (N.Drop t) = dropVal t
prim2Transform (N.Zip t) = zipVal t
prim2Transform (N.TakeWhile t) = takeWithVal t
prim2Transform (N.DropWhile t) = dropWithVal t
\end{code}
%endif

\section{The Flattening Transformation}

The flattening transformation transforms a nested program into a flat program,
in order to achieve this we transform all lambdas and replace all primitive
operations by their flat counterparts (described in the next chapter).

The transformation described in this section is very similar to the
transformation described in \cite{Jones08}. Our implementation is somewhat
different from the transformation described in \cite{Jones08} to make the result
more suitable for our execution platform, databases. As we are targeting
databases instead of GPUs or C-vector libraries. For instance it is better for
us to avoid the use index operations as these are very costly on a database. We
can, luckily, avoid the introduction of index operations.

The transformation consists out of two functions, the first merely translates a
part of an NKL tree into an FKL tree. The second however lifts such a tree into
a vector form (which is included in every function).

\begin{code} 
transform :: N.Expr            ->  TransM F.Expr
transform (N.Table t n c k)    =   pure $ F.Table t n c k
transform (N.App _t e1 e2)     =   cloAppM (transform e1) (transform e2)
transform (N.AppE1 _ p e1)     =   cloAppM (pure $ prim1Transform p) (transform e1)
transform (N.AppE2 _ p e1 e2)  =   cloAppM (cloAppM (pure $ prim2Transform p) (transform e1)) (transform e2)
transform (N.Lam t arg e)      =   do
                                    let fvs = S.toList $ N.freeVars e S.\\ S.singleton arg
                                    n <- getFreshVar
                                    cloM t n fvs arg (transform e) (lift (F.Var (listT (VarT "a")) n) e)
transform (N.If _ e1 e2 e3)    =   ifPrimM (transform e1) (transform e2) (transform e3)
transform (N.BinOp t o e1 e2)  =   opPrimM t o (transform e1) (transform e2)
transform (N.Const t v)        =   pure $ F.Const t v
transform (N.Var t x)          =   pure $ F.Var t x

\end{code}

The most interesting rule here is the rule that transforms a lambda expression into a closure. As described earlier a closure describes the variables that occur free in its body and has two bodies a `normal' body and lifted body. Primitive functions are replaced by closures, these primitives now behave as if they were ordinary lambda's. The closures however still contain some primitive, more low level, operations.

The function lift constructs the lifted bodies of lambda expressions. The extra argument is a variable which represents a list structure over which we can distribute values. This is the extra variable in the environment of a lifted closure. We shall refer to this variable as the iteration context hereinafter. 

\begin{code}
lift :: F.Expr -> N.Expr -> TransM F.Expr
lift en   (N.Table t n c k)        = pure $ distPrim ((F.Table t n c k)) en
lift en   (N.Const t v)            = pure $ distPrim (F.Const t v) en
lift _en  (N.Var t x)              = pure $ F.Var (liftType t) x
lift en   (N.App _t e1 e2)         = cloLAppM (lift en e1) (lift en e2)
lift en   (N.AppE1 _ p e1)         = cloLAppM (pure $ distPrim (prim1Transform p) en) (lift en e1) 
lift en   (N.AppE2 _ p e1 e2)      = cloLAppM (cloLAppM (pure $ distPrim (prim2Transform p) en) (lift en e1)) (lift en e2)
lift en   (N.If _ e1 e2 e3)        = do
                                      e1' <- lift en e1
                                      let (F.Var t n) = en
                                      let fvs = S.toList $ N.freeVars e2 `S.union` N.freeVars e3
                                      n1' <- getFreshVar
                                      let n1 = F.Var (typeOf en) n1'
                                      n2' <- getFreshVar
                                      let n2 = F.Var (typeOf en) n2'
                                      let rt = listT $ (unliftType t) .-> typeOf e2

                                      e2' <- cloLM rt n fvs n1' (transform e2) (lift n1 e2)
                                      
                                      e3' <- cloLM rt n fvs n2' (transform e3) (lift n2 e3) 
                                      
                                      let e2'' = restrictPrim e2' e1' `cloLApp` restrictPrim en e1'
                                      let e3'' = restrictPrim e3' (notLPrim e1') `cloLApp` restrictPrim en (notLPrim e1')
                                      
                                      pure $ combinePrim e1' e2'' e3''                                                                                                                                          
lift en   (N.BinOp t o e1 e2)      = opPrimLM t o (lift en e1) (lift en e2)
lift en   (N.Lam t arg e)          = do
                                      let (F.Var _ n') = en
                                      let fvs = S.toList $ N.freeVars e S.\\ S.singleton arg
                                      cloLM (liftType t) n' fvs arg (transform e) (lift en e)
\end{code}

Literal data and database tables are simply distributed over the iteration context. Variables are always bound in the closure, we therefor do not have to lift them (when we dist a closure over a list we actually distributed over the values contained in the closure). Top level variables do not exist in our language, they are represented by the primitives.

The primitive applications are transformed into lifted closure applications, for each primitive we defined a function. Functions are values and like literal values have to be distributed over the iteration context.

Conditional expressions are the most complicated expression to lift. It does not suffice to simply restrict the iteration context using the boolean vector and then evaluate the then and else branches. In that particular setup we would not restrict the values of variables mentioned in then and else branch. In \cite{Jones08} a case expression is used to rebind the variables after they have been restricted, however we do not have such a case expression at our disposal. Instead we construct a new lifted closure for both the then and the else branch. The argument to this closure will be a new variable, and it is exactly this variable we will lift the body of the closure over. All that is left now is that we have to apply restrict to this closure using the conditional vector (for the then branch) and the negated conditional vector (for the else branch). We then apply these closure to iteration contexts that have been restricted like wise. We then combine the results of the then and else branch into a single result vector.

Binary operators are replaced by their vector versions. And lastly lambda's are lifted similarly as in the transformation function but result in a lifted closure.
%}
