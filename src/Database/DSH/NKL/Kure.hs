{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs          #-}

-- | Infrastructure for KURE-based rewrites on NKL expressions
module Database.DSH.NKL.Kure
    ( -- * Re-export relevant KURE modules
      module Language.KURE
    , module Language.KURE.Lens

      -- * The KURE monad
    , RewriteM, RewriteStateM, TransformN, RewriteN, LensN, freshNameT
    
      -- * Setters and getters for the translation state
    , get, put, modify
    
      -- * Changing between stateful and non-stateful transforms
    , statefulT, liftstateT

      -- * The KURE context
    , NestedCtx(..), CrumbN(..), PathN, initialCtx, freeIn, boundIn
    , inScopeNames, bindVar

      -- * Congruence combinators
    , tableT, appe1T, appe2T, binopT, ifT, constExprT, varT, iteratorT, letT
    , tableR, appe1R, appe2R, binopR, ifR, litR, varR, iteratorR, letR
    
    ) where
    
       
import           Control.Monad
import           Data.Monoid

import           Language.KURE
import           Language.KURE.Lens
       
import           Database.DSH.Common.RewriteM
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Type
import           Database.DSH.NKL.Lang
                 
--------------------------------------------------------------------------------
-- Convenience type aliases

type TransformN a b = Transform NestedCtx (RewriteM Int) a b
type RewriteN a     = TransformN a a
type LensN a b      = Lens NestedCtx (RewriteM Int) a b

--------------------------------------------------------------------------------

data CrumbN = IteratorHead
            | IteratorSource
            | AppE1Arg
            | AppE2Arg1
            | AppE2Arg2
            | BinOpArg1
            | BinOpArg2
            | UnOpArg
            | LamBody
            | IfCond
            | IfThen
            | IfElse
            | LetBind
            | LetBody
            | TupleElem Int
            deriving (Eq, Show)

type AbsPathN = AbsolutePath CrumbN

type PathN = Path CrumbN

-- | The context for KURE-based NKL rewrites
data NestedCtx = NestedCtx { nkl_bindings :: [Ident]
                           , nkl_path     :: AbsPathN
                           }
                       
instance ExtendPath NestedCtx CrumbN where
    c@@n = c { nkl_path = nkl_path c @@ n }
    
instance ReadPath NestedCtx CrumbN where
    absPath c = nkl_path c

initialCtx :: [Ident] -> NestedCtx
initialCtx nameCtx = NestedCtx { nkl_bindings = nameCtx, nkl_path = mempty }

-- | Record a variable binding in the context
bindVar :: Ident -> NestedCtx -> NestedCtx
bindVar n ctx = ctx { nkl_bindings = n : nkl_bindings ctx }

inScopeNames :: NestedCtx -> [Ident]
inScopeNames = nkl_bindings

boundIn :: Ident -> NestedCtx -> Bool
boundIn n ctx = n `elem` (nkl_bindings ctx)

freeIn :: Ident -> NestedCtx -> Bool
freeIn n ctx = n `notElem` (nkl_bindings ctx)

-- | Generate a fresh name that is not bound in the current context.
freshNameT :: [Ident] -> TransformN a Ident
freshNameT avoidNames = do
    ctx <- contextT
    constT $ freshName (avoidNames ++ inScopeNames ctx)

--------------------------------------------------------------------------------
-- Support for stateful transforms

-- | Run a stateful transform with an initial state and turn it into a regular
-- (non-stateful) transform
statefulT :: s -> Transform NestedCtx (RewriteStateM s) a b -> TransformN a (s, b)
statefulT s t = resultT (stateful s) t

-- | Turn a regular rewrite into a stateful rewrite
liftstateT :: Transform NestedCtx (RewriteM Int) a b -> Transform NestedCtx (RewriteStateM s) a b
liftstateT t = resultT liftstate t

--------------------------------------------------------------------------------
-- Congruence combinators for CL expressions

tableT :: Monad m => (Type -> String -> [ColName] -> TableHints -> b)
                  -> Transform NestedCtx m Expr b
tableT f = contextfreeT $ \expr -> case expr of
                      Table ty n cs ks -> return $ f ty n cs ks
                      _                -> fail "not a table node"
{-# INLINE tableT #-}                      
                      
tableR :: Monad m => Rewrite NestedCtx m Expr
tableR = tableT Table
{-# INLINE tableR #-}

iteratorT :: Monad m => Transform NestedCtx m Expr a1
                     -> Transform NestedCtx m Expr a2
                     -> (Type -> a1 -> Ident -> a2 -> b)
                     -> Transform NestedCtx m Expr b
iteratorT t1 t2 f = transform $ \c expr -> case expr of
                     Iterator ty h x xs -> f ty <$> applyT t1 (c@@IteratorHead) h 
                                                <*> return x 
                                                <*> applyT t2 (c@@IteratorSource) xs
                     _              -> fail "not an iterator node"
{-# INLINE iteratorT #-}

iteratorR :: Monad m => Rewrite NestedCtx m Expr -> Rewrite NestedCtx m Expr -> Rewrite NestedCtx m Expr
iteratorR t1 t2 = iteratorT t1 t2 Iterator
{-# INLINE iteratorR #-}
                                       
appe1T :: Monad m => Transform NestedCtx m Expr a
                  -> (Type -> Prim1 -> a -> b)
                  -> Transform NestedCtx m Expr b
appe1T t f = transform $ \c expr -> case expr of
                      AppE1 ty p e -> f ty p <$> applyT t (c@@AppE1Arg) e                  
                      _            -> fail "not a unary primitive application"
{-# INLINE appe1T #-}                      
                      
appe1R :: Monad m => Rewrite NestedCtx m Expr -> Rewrite NestedCtx m Expr
appe1R t = appe1T t AppE1
{-# INLINE appe1R #-}                      
                      
appe2T :: Monad m => Transform NestedCtx m Expr a1
                  -> Transform NestedCtx m Expr a2
                  -> (Type -> Prim2 -> a1 -> a2 -> b)
                  -> Transform NestedCtx m Expr b
appe2T t1 t2 f = transform $ \c expr -> case expr of
                     AppE2 ty p e1 e2 -> f ty p <$> applyT t1 (c@@AppE2Arg1) e1 
                                                <*> applyT t2 (c@@AppE2Arg2) e2
                     _                -> fail "not a binary primitive application"
{-# INLINE appe2T #-}                      

appe2R :: Monad m => Rewrite NestedCtx m Expr -> Rewrite NestedCtx m Expr -> Rewrite NestedCtx m Expr
appe2R t1 t2 = appe2T t1 t2 AppE2
{-# INLINE appe2R #-}                      
                     
binopT :: Monad m => Transform NestedCtx m Expr a1
                  -> Transform NestedCtx m Expr a2
                  -> (Type -> ScalarBinOp -> a1 -> a2 -> b)
                  -> Transform NestedCtx m Expr b
binopT t1 t2 f = transform $ \c expr -> case expr of
                     BinOp ty op e1 e2 -> f ty op <$> applyT t1 (c@@BinOpArg1) e1 
                                                  <*> applyT t2 (c@@BinOpArg2) e2
                     _                 -> fail "not a binary operator application"
{-# INLINE binopT #-}                      

binopR :: Monad m => Rewrite NestedCtx m Expr -> Rewrite NestedCtx m Expr -> Rewrite NestedCtx m Expr
binopR t1 t2 = binopT t1 t2 BinOp
{-# INLINE binopR #-}                      

unopT :: Monad m => Transform NestedCtx m Expr a
                 -> (Type -> ScalarUnOp -> a -> b)
                 -> Transform NestedCtx m Expr b
unopT t f = transform $ \ctx expr -> case expr of
                     UnOp ty op e -> f ty op <$> applyT t (ctx@@UnOpArg) e
                     _            -> fail "not an unary operator application"
{-# INLINE unopT #-}

unopR :: Monad m => Rewrite NestedCtx m Expr -> Rewrite NestedCtx m Expr
unopR t = unopT t UnOp
{-# INLINE unopR #-}
                     
ifT :: Monad m => Transform NestedCtx m Expr a1
               -> Transform NestedCtx m Expr a2
               -> Transform NestedCtx m Expr a3
               -> (Type -> a1 -> a2 -> a3 -> b)
               -> Transform NestedCtx m Expr b
ifT t1 t2 t3 f = transform $ \c expr -> case expr of
                    If ty e1 e2 e3 -> f ty <$> applyT t1 (c@@IfCond) e1               
                                           <*> applyT t2 (c@@IfThen) e2
                                           <*> applyT t3 (c@@IfElse) e3
                    _              -> fail "not an if expression"
{-# INLINE ifT #-}                      
                    
ifR :: Monad m => Rewrite NestedCtx m Expr
               -> Rewrite NestedCtx m Expr
               -> Rewrite NestedCtx m Expr
               -> Rewrite NestedCtx m Expr
ifR t1 t2 t3 = ifT t1 t2 t3 If               
{-# INLINE ifR #-}                      
                    
constExprT :: Monad m => (Type -> Val -> b) -> Transform NestedCtx m Expr b
constExprT f = contextfreeT $ \expr -> case expr of
                    Const ty v -> return $ f ty v
                    _          -> fail "not a constant"
{-# INLINE constExprT #-}                      
                    
litR :: Monad m => Rewrite NestedCtx m Expr
litR = constExprT Const
{-# INLINE litR #-}                      
                    
varT :: Monad m => (Type -> Ident -> b) -> Transform NestedCtx m Expr b
varT f = contextfreeT $ \expr -> case expr of
                    Var ty n -> return $ f ty n
                    _        -> fail "not a variable"
{-# INLINE varT #-}                      
                    
varR :: Monad m => Rewrite NestedCtx m Expr
varR = varT Var
{-# INLINE varR #-}                      

letT :: Monad m => Transform NestedCtx m Expr a1
                -> Transform NestedCtx m Expr a2
                -> (Type -> Ident -> a1 -> a2 -> b) 
                -> Transform NestedCtx m Expr b
letT t1 t2 f = transform $ \c expr -> case expr of
                 Let ty x xs e -> f ty x <$> applyT t1 (c@@LetBind) xs 
                                         <*> applyT t2 (bindVar x $ c@@LetBody) e
                 _             -> fail "not a let expression"

letR :: Monad m => Rewrite NestedCtx m Expr 
                -> Rewrite NestedCtx m Expr 
                -> Rewrite NestedCtx m Expr
letR r1 r2 = letT r1 r2 Let

mkTupleT :: Monad m => Transform NestedCtx m Expr a
                    -> (Type -> [a] -> b)
                    -> Transform NestedCtx m Expr b
mkTupleT t f = transform $ \c expr -> case expr of
                   MkTuple ty es -> f ty <$> zipWithM (\e i -> applyT t (c@@TupleElem i) e) es [1..]
                   _             -> fail "not a tuple constructor"
{-# INLINE mkTupleT #-}

mkTupleR :: Monad m => Rewrite NestedCtx m Expr -> Rewrite NestedCtx m Expr
mkTupleR r = mkTupleT r MkTuple


--------------------------------------------------------------------------------
       
instance Walker NestedCtx Expr where
    allR :: forall m. MonadCatch m => Rewrite NestedCtx m Expr -> Rewrite NestedCtx m Expr
    allR r = readerT $ \e -> case e of
            Table{}    -> idR
            AppE1{}    -> appe1R (extractR r)
            AppE2{}    -> appe2R (extractR r) (extractR r)
            BinOp{}    -> binopR (extractR r) (extractR r)
            UnOp{}     -> unopR (extractR r)
            Iterator{} -> iteratorR (extractR r) (extractR r)
            If{}       -> ifR (extractR r) (extractR r) (extractR r)
            Const{}    -> idR
            Var{}      -> idR
            Let{}      -> letR (extractR r) (extractR r)
            MkTuple{}  -> mkTupleR (extractR r)
            
--------------------------------------------------------------------------------
-- I find it annoying that Applicative is not a superclass of Monad.

(<$>) :: Monad m => (a -> b) -> m a -> m b
(<$>) = liftM
{-# INLINE (<$>) #-}

(<*>) :: Monad m => m (a -> b) -> m a -> m b
(<*>) = ap
{-# INLINE (<*>) #-}

