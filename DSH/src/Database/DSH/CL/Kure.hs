{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs          #-}

-- | Infrastructure for KURE-based rewrites on CL expressions
   
module Database.DSH.CL.Kure
    ( -- * Re-export relevant KURE modules
      module Language.KURE
    , module Language.KURE.Lens

      -- * The KURE monad
    , CompM, CompSM, TranslateC, RewriteC, LensC, freshName
    
      -- * Setters and getters for the translation state
    , get, put, modify
    
      -- * Changing between stateful and non-stateful translates
    , statefulT, liftstateT

      -- * The KURE context
    , CompCtx(..), PathC, initialCtx, freeIn, boundIn, inScopeVars, bindQual, bindVar

      -- * Congruence combinators
    , tableT, appT, appe1T, appe2T, binopT, lamT, ifT, litT, varT, compT
    , tableR, appR, appe1R, appe2R, binopR, lamR, ifR, litR, varR, compR
    , bindQualT, guardQualT, bindQualR, guardQualR
    , qualsT, qualsR, qualsemptyT, qualsemptyR
    
      -- * The sum type
    , CL(..)
    ) where
    
       
import           Control.Monad
import           Data.Monoid
import qualified Data.Map as M
import qualified Data.Foldable as F

import           Language.KURE
import           Language.KURE.Lens
       
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Monad
                 
--------------------------------------------------------------------------------
-- Convenience type aliases

type TranslateC a b = Translate CompCtx (CompM Int) a b
type RewriteC a     = TranslateC a a
type LensC a b      = Lens CompCtx (CompM Int) a b

--------------------------------------------------------------------------------

type AbsPathC = AbsolutePath Int

type PathC = Path Int

-- | The context for KURE-based CL rewrites
data CompCtx = CompCtx { cl_bindings :: M.Map Ident Type 
                       , cl_path     :: AbsPathC
                       }
                       
instance ExtendPath CompCtx Int where
    c@@n = c { cl_path = cl_path c @@ n }
    
instance ReadPath CompCtx Int where
    absPath c = cl_path c

initialCtx :: CompCtx
initialCtx = CompCtx { cl_bindings = M.empty, cl_path = mempty }

-- | Record a variable binding in the context
bindVar :: Ident -> Type -> CompCtx -> CompCtx
bindVar n ty ctx = ctx { cl_bindings = M.insert n ty (cl_bindings ctx) }

-- | If the qualifier represents a generator, bind the variable in the context.
bindQual :: CompCtx -> Qual -> CompCtx
bindQual ctx (BindQ n e) = bindVar n (elemT $ typeOf e) ctx
bindQual ctx _           = ctx
         
inScopeVars :: CompCtx -> [Ident]
inScopeVars = M.keys . cl_bindings

boundIn :: Ident -> CompCtx -> Bool
boundIn n ctx = n `M.member` (cl_bindings ctx)

freeIn :: Ident -> CompCtx -> Bool
freeIn n ctx = n `M.notMember` (cl_bindings ctx)

--------------------------------------------------------------------------------
-- Support for stateful translates

-- | Run a stateful translate with an initial state and turn it into a regular
-- (non-stateful) translate
statefulT :: s -> Translate CompCtx (CompSM s) a b -> TranslateC a (s, b)
statefulT s t = resultT (stateful s) t

-- | Turn a regular rewrite into a stateful rewrite
liftstateT :: Translate CompCtx (CompM Int) a b -> Translate CompCtx (CompSM s) a b
liftstateT t = resultT liftstate t

--------------------------------------------------------------------------------
-- Congruence combinators for CL expressions

tableT :: Monad m => (Type -> String -> [Column] -> [Key] -> b)
                  -> Translate CompCtx m Expr b
tableT f = contextfreeT $ \expr -> case expr of
                      Table ty n cs ks -> return $ f ty n cs ks
                      _                -> fail "not a table node"
{-# INLINE tableT #-}                      
                      
tableR :: Monad m => Rewrite CompCtx m Expr
tableR = tableT Table
{-# INLINE tableR #-}
                                       
appT :: Monad m => Translate CompCtx m Expr a1
                -> Translate CompCtx m Expr a2
                -> (Type -> a1 -> a2 -> b)
                -> Translate CompCtx m Expr b
appT t1 t2 f = translate $ \c expr -> case expr of
                      App ty e1 e2 -> f ty <$> apply t1 (c@@0) e1 <*> apply t2 (c@@1) e2
                      _            -> fail "not an application node"
{-# INLINE appT #-}                      

appR :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr
appR t1 t2 = appT t1 t2 App
{-# INLINE appR #-}                      
                      
appe1T :: Monad m => Translate CompCtx m Expr a
                  -> (Type -> Prim1 Type -> a -> b)
                  -> Translate CompCtx m Expr b
appe1T t f = translate $ \c expr -> case expr of
                      AppE1 ty p e -> f ty p <$> apply t (c@@0) e                  
                      _            -> fail "not a unary primitive application"
{-# INLINE appe1T #-}                      
                      
appe1R :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr
appe1R t = appe1T t AppE1
{-# INLINE appe1R #-}                      
                      
appe2T :: Monad m => Translate CompCtx m Expr a1
                  -> Translate CompCtx m Expr a2
                  -> (Type -> Prim2 Type -> a1 -> a2 -> b)
                  -> Translate CompCtx m Expr b
appe2T t1 t2 f = translate $ \c expr -> case expr of
                     AppE2 ty p e1 e2 -> f ty p <$> apply t1 (c@@0) e1 <*> apply t2 (c@@1) e2
                     _                -> fail "not a binary primitive application"
{-# INLINE appe2T #-}                      

appe2R :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr
appe2R t1 t2 = appe2T t1 t2 AppE2
{-# INLINE appe2R #-}                      
                     
binopT :: Monad m => Translate CompCtx m Expr a1
                  -> Translate CompCtx m Expr a2
                  -> (Type -> Oper -> a1 -> a2 -> b)
                  -> Translate CompCtx m Expr b
binopT t1 t2 f = translate $ \c expr -> case expr of
                     BinOp ty op e1 e2 -> f ty op <$> apply t1 (c@@0) e1 <*> apply t2 (c@@1) e2
                     _                 -> fail "not a binary operator application"
{-# INLINE binopT #-}                      

binopR :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr
binopR t1 t2 = binopT t1 t2 BinOp
{-# INLINE binopR #-}                      
                     
lamT :: Monad m => Translate CompCtx m Expr a
                -> (Type -> Ident -> a -> b)
                -> Translate CompCtx m Expr b
lamT t f = translate $ \c expr -> case expr of
                     Lam ty n e -> f ty n <$> apply t (bindVar n (domainT ty) c@@0) e
                     _          -> fail "not a lambda"
{-# INLINE lamT #-}                      
                     
lamR :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr
lamR t = lamT t Lam
{-# INLINE lamR #-}                      
                     
ifT :: Monad m => Translate CompCtx m Expr a1
               -> Translate CompCtx m Expr a2
               -> Translate CompCtx m Expr a3
               -> (Type -> a1 -> a2 -> a3 -> b)
               -> Translate CompCtx m Expr b
ifT t1 t2 t3 f = translate $ \c expr -> case expr of
                    If ty e1 e2 e3 -> f ty <$> apply t1 (c@@0) e1               
                                           <*> apply t2 (c@@1) e2
                                           <*> apply t3 (c@@2) e3
                    _              -> fail "not an if expression"
{-# INLINE ifT #-}                      
                    
ifR :: Monad m => Rewrite CompCtx m Expr
               -> Rewrite CompCtx m Expr
               -> Rewrite CompCtx m Expr
               -> Rewrite CompCtx m Expr
ifR t1 t2 t3 = ifT t1 t2 t3 If               
{-# INLINE ifR #-}                      
                    
litT :: Monad m => (Type -> Val -> b) -> Translate CompCtx m Expr b
litT f = contextfreeT $ \expr -> case expr of
                    Lit ty v -> return $ f ty v
                    _          -> fail "not a constant"
{-# INLINE litT #-}                      
                    
litR :: Monad m => Rewrite CompCtx m Expr
litR = litT Lit
{-# INLINE litR #-}                      
                    
varT :: Monad m => (Type -> Ident -> b) -> Translate CompCtx m Expr b
varT f = contextfreeT $ \expr -> case expr of
                    Var ty n -> return $ f ty n
                    _        -> fail "not a variable"
{-# INLINE varT #-}                      
                    
varR :: Monad m => Rewrite CompCtx m Expr
varR = varT Var
{-# INLINE varR #-}                      

compT :: Monad m => Translate CompCtx m Expr a1
                 -> Translate CompCtx m (NL Qual) a2
                 -> (Type -> a1 -> a2 -> b)
                 -> Translate CompCtx m Expr b
compT t1 t2 f = translate $ \ctx expr -> case expr of
                    Comp ty e qs -> f ty <$> apply t1 (F.foldl' bindQual (ctx@@0) qs) e 
                                         <*> apply t2 (ctx@@1) qs
                    _            -> fail "not a comprehension"
{-# INLINE compT #-}                      
                    
compR :: Monad m => Rewrite CompCtx m Expr
                 -> Rewrite CompCtx m (NL Qual)
                 -> Rewrite CompCtx m Expr
compR t1 t2 = compT t1 t2 Comp                 
{-# INLINE compR #-}                      

--------------------------------------------------------------------------------
-- Congruence combinators for qualifiers

bindQualT :: Monad m => Translate CompCtx m Expr a 
                     -> (Ident -> a -> b) 
                     -> Translate CompCtx m Qual b
bindQualT t f = translate $ \ctx expr -> case expr of
                BindQ n e -> f n <$> apply t (ctx@@0) e
                _         -> fail "not a generator"
{-# INLINE bindQualT #-}                      
                
bindQualR :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Qual
bindQualR t = bindQualT t BindQ
{-# INLINE bindQualR #-}                      

guardQualT :: Monad m => Translate CompCtx m Expr a 
                      -> (a -> b) 
                      -> Translate CompCtx m Qual b
guardQualT t f = translate $ \ctx expr -> case expr of
                GuardQ e -> f <$> apply t (ctx@@0) e
                _        -> fail "not a guard"
{-# INLINE guardQualT #-}                      
                
guardQualR :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Qual
guardQualR t = guardQualT t GuardQ
{-# INLINE guardQualR #-}                      

--------------------------------------------------------------------------------
-- Congruence combinator for a qualifier list

qualsT :: Monad m => Translate CompCtx m Qual a1
                  -> Translate CompCtx m (NL Qual) a2
                  -> (a1 -> a2 -> b) 
                  -> Translate CompCtx m (NL Qual) b
qualsT t1 t2 f = translate $ \ctx quals -> case quals of
                   q :* qs -> f <$> apply t1 (ctx@@0) q <*> apply t2 (bindQual (ctx@@0) q) qs
                   S _     -> fail "not a nonempty cons"
{-# INLINE qualsT #-}                      
                   
qualsR :: Monad m => Rewrite CompCtx m Qual
                  -> Rewrite CompCtx m (NL Qual)
                  -> Rewrite CompCtx m (NL Qual)
qualsR t1 t2 = qualsT t1 t2 (:*)                  
{-# INLINE qualsR #-}                      

                   
qualsemptyT :: Monad m => Translate CompCtx m Qual a
                       -> (a -> b)
                       -> Translate CompCtx m (NL Qual) b
qualsemptyT t f = translate $ \ctx quals -> case quals of
                      S q -> f <$> apply t (ctx@@0) q
                      _   -> fail "not a nonempty singleton"
{-# INLINE qualsemptyT #-}                      
                      
qualsemptyR :: Monad m => Rewrite CompCtx m Qual
                       -> Rewrite CompCtx m (NL Qual)
qualsemptyR t = qualsemptyT t S                       
{-# INLINE qualsemptyR #-}                      

--------------------------------------------------------------------------------
       
-- | The sum type of *nodes* considered for KURE traversals
data CL = ExprCL Expr
        | QualCL Qual
        | QualsCL (NL Qual)
        deriving (Show)
        
instance Injection Expr CL where
    inject                = ExprCL
    
    project (ExprCL expr) = Just expr
    project _             = Nothing

instance Injection Qual CL where
    inject             = QualCL
    
    project (QualCL q) = Just q
    project _          = Nothing
    
instance Injection (NL Qual) CL where
    inject               = QualsCL
    
    project (QualsCL qs) = Just qs
    project _            = Nothing

    
instance Walker CompCtx CL where
    allR :: forall m. MonadCatch m => Rewrite CompCtx m CL -> Rewrite CompCtx m CL
    allR r = promoteR allRexpr <+ promoteR allRqual <+ promoteR allRquals
    
      where
        allRquals = qualsR (extractR r) (extractR r) <+ qualsemptyR (extractR r)
        {-# INLINE allRquals #-}

        allRqual = bindQualR (extractR r) <+ guardQualR (extractR r)
        {-# INLINE allRqual #-}

        allRexpr = varR <+ litR <+ tableR
                   <+ ifR (extractR r) (extractR r) (extractR r)
                   <+ appR (extractR r) (extractR r)
                   <+ appe1R (extractR r)
                   <+ appe2R (extractR r) (extractR r)
                   <+ binopR (extractR r) (extractR r)
                   <+ lamR (extractR r)
                   <+ compR (extractR r) (extractR r)
        {-# INLINE allRexpr #-}
         

--------------------------------------------------------------------------------
-- A Walker instance for polymorphic NL lists so that we can use the traversal
-- infrastructure on lists.
   
consT :: Monad m => Translate CompCtx m (NL a) b
                 -> (a -> b -> c)
                 -> Translate CompCtx m (NL a) c
consT t f = translate $ \ctx nl -> case nl of
                a :* as -> f a <$> apply t (ctx@@0) as
                S _     -> fail "not a nonempty cons"
{-# INLINE consT #-}                      
                    
consR :: Monad m => Rewrite CompCtx m (NL a) 
                 -> Rewrite CompCtx m (NL a)
consR t = consT t (:*)                 
{-# INLINE consR #-}                      

singletonT :: Monad m => (a -> c)
                      -> Translate CompCtx m (NL a) c
singletonT f = contextfreeT $ \nl -> case nl of
                   S a    -> return $ f a
                   _ :* _ -> fail "not a nonempty singleton"
{-# INLINE singletonT #-}                      
               
singletonR :: Monad m => Rewrite CompCtx m (NL a)
singletonR = singletonT S                      
{-# INLINE singletonR #-}                      
                   
instance Walker CompCtx (NL a) where
    allR r = consR r <+ singletonR
    
--------------------------------------------------------------------------------
-- I find it annoying that Applicative is not a superclass of Monad.

(<$>) :: Monad m => (a -> b) -> m a -> m b
(<$>) = liftM
{-# INLINE (<$>) #-}

(<*>) :: Monad m => m (a -> b) -> m a -> m b
(<*>) = ap
{-# INLINE (<*>) #-}

