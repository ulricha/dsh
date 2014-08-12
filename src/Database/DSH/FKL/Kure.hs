{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs          #-}

-- | Infrastructure for KURE-based rewrites on NKL expressions
module Database.DSH.FKL.Kure
    ( -- * Re-export relevant KURE modules
      module Language.KURE
    , module Language.KURE.Lens

      -- * The KURE monad
    , RewriteM, RewriteStateM, TransformF, RewriteF, LensF, freshNameT
    
      -- * Setters and getters for the translation state
    , get, put, modify
    
      -- * Changing between stateful and non-stateful transforms
    , statefulT, liftstateT

      -- * The KURE context
    , FlatCtx(..), CrumbF(..), PathF, initialCtx, freeIn, boundIn
    , inScopeNames, bindVar

      -- * Congruence combinators
    , tableT, cloappT, clolappT, papp1T, papp2T, papp3T, binopT, unopT
    , cloT, acloT, ifT, constExprT, varT

    , tableR, cloappR, clolappR, papp1R, papp2R, papp3R, binopR, unopR
    , cloR, acloR, ifR, constExprR, varR
    
    ) where
    
       
import           Control.Monad
import           Data.Monoid

import           Language.KURE
import           Language.KURE.Lens
       
import           Database.DSH.Common.RewriteM
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Type
import           Database.DSH.FKL.Lang
                 
--------------------------------------------------------------------------------
-- Convenience type aliases

type TransformF a b = Transform FlatCtx (RewriteM Int) a b
type RewriteF a     = TransformF a a
type LensF a b      = Lens FlatCtx (RewriteM Int) a b

--------------------------------------------------------------------------------

data CrumbF = AppFun
            | PApp1Arg
            | PApp2Arg1
            | PApp2Arg2
            | PApp3Arg1
            | PApp3Arg2
            | PApp3Arg3
            | CloAppFun
            | CloAppArg
            | CloLAppFun
            | CloLAppArg
            | BinOpArg1
            | BinOpArg2
            | UnOpArg
            | IfCond
            | IfThen
            | IfElse
            | CloBody
            | CloLBody
            | ACloBody
            | ACloLBody
            deriving (Eq, Show)

type AbsPathF = AbsolutePath CrumbF

type PathF = Path CrumbF

-- | The context for KURE-based FKL rewrites
data FlatCtx = FlatCtx { fkl_bindings :: [Ident]
                       , fkl_path     :: AbsPathF
                       }
                       
instance ExtendPath FlatCtx CrumbF where
    c@@n = c { fkl_path = fkl_path c @@ n }
    
instance ReadPath FlatCtx CrumbF where
    absPath c = fkl_path c

initialCtx :: FlatCtx
initialCtx = FlatCtx { fkl_bindings = [], fkl_path = mempty }

-- | Record a variable binding in the context
bindVar :: Ident -> FlatCtx -> FlatCtx
bindVar n ctx = ctx { fkl_bindings = n : fkl_bindings ctx }

inScopeNames :: FlatCtx -> [Ident]
inScopeNames = fkl_bindings

boundIn :: Ident -> FlatCtx -> Bool
boundIn n ctx = n `elem` (fkl_bindings ctx)

freeIn :: Ident -> FlatCtx -> Bool
freeIn n ctx = n `notElem` (fkl_bindings ctx)

-- | Generate a fresh name that is not bound in the current context.
freshNameT :: [Ident] -> TransformF a Ident
freshNameT avoidNames = do
    ctx <- contextT
    constT $ freshName (avoidNames ++ inScopeNames ctx)

--------------------------------------------------------------------------------
-- Support for stateful transforms

-- | Run a stateful transform with an initial state and turn it into a regular
-- (non-stateful) transform
statefulT :: s -> Transform FlatCtx (RewriteStateM s) a b -> TransformF a (s, b)
statefulT s t = resultT (stateful s) t

-- | Turn a regular rewrite into a stateful rewrite
liftstateT :: Transform FlatCtx (RewriteM Int) a b -> Transform FlatCtx (RewriteStateM s) a b
liftstateT t = resultT liftstate t

--------------------------------------------------------------------------------
-- Congruence combinators for FKL expressions

tableT :: Monad m => (Type -> String -> [Column] -> TableHints -> b)
                  -> Transform FlatCtx m Expr b
tableT f = contextfreeT $ \expr -> case expr of
                      Table ty n cs ks -> return $ f ty n cs ks
                      _                -> fail "not a table node"
{-# INLINE tableT #-}                      

                      
tableR :: Monad m => Rewrite FlatCtx m Expr
tableR = tableT Table
{-# INLINE tableR #-}

ifT :: Monad m => Transform FlatCtx m Expr a1
               -> Transform FlatCtx m Expr a2
               -> Transform FlatCtx m Expr a3
               -> (Type -> a1 -> a2 -> a3 -> b)
               -> Transform FlatCtx m Expr b
ifT t1 t2 t3 f = transform $ \c expr -> case expr of
                    If ty e1 e2 e3 -> f ty <$> apply t1 (c@@IfCond) e1               
                                           <*> apply t2 (c@@IfThen) e2
                                           <*> apply t3 (c@@IfElse) e3
                    _              -> fail "not an if expression"
{-# INLINE ifT #-}                      
                    
ifR :: Monad m => Rewrite FlatCtx m Expr
               -> Rewrite FlatCtx m Expr
               -> Rewrite FlatCtx m Expr
               -> Rewrite FlatCtx m Expr
ifR t1 t2 t3 = ifT t1 t2 t3 If               
{-# INLINE ifR #-}                      

varT :: Monad m => (Type -> Ident -> b) -> Transform FlatCtx m Expr b
varT f = contextfreeT $ \expr -> case expr of
                    Var ty n -> return $ f ty n
                    _        -> fail "not a variable"
{-# INLINE varT #-}                      
                    
varR :: Monad m => Rewrite FlatCtx m Expr
varR = varT Var
{-# INLINE varR #-}                      

binopT :: Monad m => Transform FlatCtx m Expr a1
                  -> Transform FlatCtx m Expr a2
                  -> (Type -> Lifted ScalarBinOp -> a1 -> a2 -> b)
                  -> Transform FlatCtx m Expr b
binopT t1 t2 f = transform $ \c expr -> case expr of
                     BinOp ty op e1 e2 -> f ty op <$> apply t1 (c@@BinOpArg1) e1 <*> apply t2 (c@@BinOpArg2) e2
                     _                 -> fail "not a binary operator application"
{-# INLINE binopT #-}                      

binopR :: Monad m => Rewrite FlatCtx m Expr -> Rewrite FlatCtx m Expr -> Rewrite FlatCtx m Expr
binopR t1 t2 = binopT t1 t2 BinOp
{-# INLINE binopR #-}                      

unopT :: Monad m => Transform FlatCtx m Expr a
                 -> (Type -> Lifted ScalarUnOp -> a -> b)
                 -> Transform FlatCtx m Expr b
unopT t f = transform $ \ctx expr -> case expr of
                     UnOp ty op e -> f ty op <$> apply t (ctx@@UnOpArg) e
                     _            -> fail "not an unary operator application"
{-# INLINE unopT #-}

unopR :: Monad m => Rewrite FlatCtx m Expr -> Rewrite FlatCtx m Expr
unopR t = unopT t UnOp
{-# INLINE unopR #-}
                     
papp1T :: Monad m => Transform FlatCtx m Expr a
                  -> (Type -> Prim1 -> a -> b)
                  -> Transform FlatCtx m Expr b
papp1T t f = transform $ \c expr -> case expr of
                      PApp1 ty p e -> f ty p <$> apply t (c@@PApp1Arg) e                  
                      _            -> fail "not a unary primitive application"
{-# INLINE papp1T #-}                      
                      
papp1R :: Monad m => Rewrite FlatCtx m Expr -> Rewrite FlatCtx m Expr
papp1R t = papp1T t PApp1
{-# INLINE papp1R #-}                      

                      
papp2T :: Monad m => Transform FlatCtx m Expr a1
                  -> Transform FlatCtx m Expr a2
                  -> (Type -> Prim2 -> a1 -> a2 -> b)
                  -> Transform FlatCtx m Expr b
papp2T t1 t2 f = transform $ \c expr -> case expr of
                     PApp2 ty p e1 e2 -> f ty p <$> apply t1 (c@@PApp2Arg1) e1 <*> apply t2 (c@@PApp2Arg2) e2
                     _                -> fail "not a binary primitive application"
{-# INLINE papp2T #-}                      

papp2R :: Monad m => Rewrite FlatCtx m Expr -> Rewrite FlatCtx m Expr -> Rewrite FlatCtx m Expr
papp2R t1 t2 = papp2T t1 t2 PApp2
{-# INLINE papp2R #-}                      

papp3T :: Monad m => Transform FlatCtx m Expr a1
                  -> Transform FlatCtx m Expr a2
                  -> Transform FlatCtx m Expr a3
                  -> (Type -> Prim3 -> a1 -> a2 -> a3 -> b)
                  -> Transform FlatCtx m Expr b
papp3T t1 t2 t3 f = transform $ \c expr -> case expr of
                     PApp3 ty p e1 e2 e3 -> f ty p 
                                            <$> apply t1 (c@@PApp3Arg1) e1 
                                            <*> apply t2 (c@@PApp3Arg2) e2
                                            <*> apply t3 (c@@PApp3Arg3) e3
                     _                -> fail "not a ternary primitive application"
{-# INLINE papp3T #-}                      

papp3R :: Monad m 
       => Rewrite FlatCtx m Expr 
       -> Rewrite FlatCtx m Expr 
       -> Rewrite FlatCtx m Expr 
       -> Rewrite FlatCtx m Expr
papp3R t1 t2 t3 = papp3T t1 t2 t3 PApp3
{-# INLINE papp3R #-}                      

cloappT :: Monad m => Transform FlatCtx m Expr a1
                   -> Transform FlatCtx m Expr a2
                   -> (Type -> a1 -> a2 -> b)
                   -> Transform FlatCtx m Expr b
cloappT t1 t2 f = transform $ \c expr -> case expr of
                      CloApp ty e1 e2 -> f ty <$> apply t1 (c@@CloAppFun) e1 <*> apply t2 (c@@CloAppArg) e2
                      _               -> fail "not a closure application node"
{-# INLINE cloappT #-}                      

cloappR :: Monad m => Rewrite FlatCtx m Expr -> Rewrite FlatCtx m Expr -> Rewrite FlatCtx m Expr
cloappR t1 t2 = cloappT t1 t2 CloApp
{-# INLINE cloappR #-}                      

clolappT :: Monad m => Transform FlatCtx m Expr a1
                   -> Transform FlatCtx m Expr a2
                   -> (Type -> a1 -> a2 -> b)
                   -> Transform FlatCtx m Expr b
clolappT t1 t2 f = transform $ \c expr -> case expr of
                      CloLApp ty e1 e2 -> f ty <$> apply t1 (c@@CloLAppFun) e1 <*> apply t2 (c@@CloLAppArg) e2
                      _               -> fail "not a lifted closure application node"
{-# INLINE clolappT #-}                      

clolappR :: Monad m => Rewrite FlatCtx m Expr -> Rewrite FlatCtx m Expr -> Rewrite FlatCtx m Expr
clolappR t1 t2 = clolappT t1 t2 CloLApp
{-# INLINE clolappR #-}                      

constExprT :: Monad m => (Type -> Val -> b) -> Transform FlatCtx m Expr b
constExprT f = contextfreeT $ \expr -> case expr of
                    Const ty v -> return $ f ty v
                    _          -> fail "not a constant"
{-# INLINE constExprT #-}                      
                    
constExprR :: Monad m => Rewrite FlatCtx m Expr
constExprR = constExprT Const
{-# INLINE constExprR #-}                      
                    
                      
cloT :: Monad m => Transform FlatCtx m Expr a1
                -> Transform FlatCtx m Expr a2
                -> (Type -> Ident -> [Ident] -> Ident -> a1 -> a2 -> b)
                -> Transform FlatCtx m Expr b
cloT t1 t2 f = transform $ \c expr -> case expr of
                     -- FIXME when traversing into the bodies we
                     -- propably should bind the variables from the
                     -- closure environment in the context
                     -- environment.
                     Clo ty envName envNames x body liftedBody -> 
                         f ty envName envNames x
                         <$> apply t1 (bindVar x c@@CloBody) body
                         <*> apply t2 (bindVar x c@@CloLBody) liftedBody
                                                  
                     _          -> fail "not a closure"
{-# INLINE cloT #-}                      
                     
cloR :: Monad m 
     => Rewrite FlatCtx m Expr 
     -> Rewrite FlatCtx m Expr 
     -> Rewrite FlatCtx m Expr
cloR t1 t2 = cloT t1 t2 Clo
{-# INLINE cloR #-}                      
                     
acloT :: Monad m => Transform FlatCtx m Expr a1
                -> Transform FlatCtx m Expr a2
                -> (Type -> Ident -> [Ident] -> Ident -> a1 -> a2 -> b)
                -> Transform FlatCtx m Expr b
acloT t1 t2 f = transform $ \c expr -> case expr of
                     -- FIXME when traversing into the bodies we
                     -- propably should bind the variables from the
                     -- closure environment in the context
                     -- environment.
                     AClo ty envName envNames x body liftedBody -> 
                         f ty envName envNames x
                         <$> apply t1 (bindVar x c@@ACloBody) body
                         <*> apply t2 (bindVar x c@@ACloLBody) liftedBody
                                                  
                     _          -> fail "not an a closure"
{-# INLINE acloT #-}                      
                     
acloR :: Monad m 
      => Rewrite FlatCtx m Expr 
      -> Rewrite FlatCtx m Expr 
      -> Rewrite FlatCtx m Expr
acloR t1 t2 = acloT t1 t2 AClo
{-# INLINE acloR #-}                      


--------------------------------------------------------------------------------
       
instance Walker FlatCtx Expr where
    allR :: forall m. MonadCatch m => Rewrite FlatCtx m Expr -> Rewrite FlatCtx m Expr
    allR r = readerT $ \e -> case e of
            Table{}   -> idR
            CloApp{}  -> cloappR (extractR r) (extractR r)
            CloLApp{} -> clolappR (extractR r) (extractR r)
            PApp1{}   -> papp1R (extractR r)
            PApp2{}   -> papp2R (extractR r) (extractR r)
            PApp3{}   -> papp3R (extractR r) (extractR r) (extractR r)
            BinOp{}   -> binopR (extractR r) (extractR r)
            UnOp{}    -> unopR (extractR r)
            Clo{}     -> cloR (extractR r) (extractR r)
            AClo{}    -> acloR (extractR r) (extractR r)
            If{}      -> ifR (extractR r) (extractR r) (extractR r)
            Const{}   -> idR
            Var{}     -> idR

--------------------------------------------------------------------------------
-- I find it annoying that Applicative is not a superclass of Monad.

(<$>) :: Monad m => (a -> b) -> m a -> m b
(<$>) = liftM
{-# INLINE (<$>) #-}

(<*>) :: Monad m => m (a -> b) -> m a -> m b
(<*>) = ap
{-# INLINE (<*>) #-}

