{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs          #-}

-- | Infrastructure for KURE-based rewrites on CL expressions
   
module Database.DSH.CL.Kure
    ( -- * Re-export relevant KURE modules
      module Language.KURE

      -- * The KURE monad
    , CompM, TranslateC, RewriteC, freshName

      -- * The KURE context
    , CompCtx, initialCtx, freeIn, boundIn, inScopeVars

      -- * Congruence combinators
    , tableT, appT, appe1T, appe2T, binopT, lamT, ifT, litT, varT, compT
    , tableR, appR, appe1R, appe2R, binopR, lamR, ifR, litR, varR, compR
    , bindQualT, guardQualT, bindQualR, guardQualR
    , qualsT, qualsR
    
      -- * The sum type
    , CL
    ) where
    
       
import           Control.Monad
import qualified Data.Map as M
import qualified Data.Foldable as F

import           Language.KURE
       
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Monad
                 
--------------------------------------------------------------------------------
-- Convenience type aliases

type TranslateC a b = Translate CompCtx CompM a b
type RewriteC a     = TranslateC a a

--------------------------------------------------------------------------------

-- | The context for KURE-based CL rewrites
data CompCtx = CompCtx { cl_bindings :: M.Map Ident Type }

initialCtx :: CompCtx
initialCtx = CompCtx { cl_bindings = M.empty }

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
-- Congruence combinators for CL expressions

tableT :: Monad m => (Type -> String -> [Column] -> [Key] -> b)
                  -> Translate CompCtx m Expr b
tableT f = contextfreeT $ \expr -> case expr of
                      Table ty n cs ks -> return $ f ty n cs ks
                      _                -> fail "not a table node"
                      
tableR :: Monad m => Rewrite CompCtx m Expr
tableR = tableT Table
                                       
appT :: Monad m => Translate CompCtx m Expr a1
                -> Translate CompCtx m Expr a2
                -> (Type -> a1 -> a2 -> b)
                -> Translate CompCtx m Expr b
appT t1 t2 f = translate $ \c expr -> case expr of
                      App ty e1 e2 -> f ty <$> apply t1 c e1 <*> apply t2 c e2
                      _            -> fail "not an application node"
                      
appR :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr
appR t1 t2 = appT t1 t2 App
                      
appe1T :: Monad m => Translate CompCtx m Expr a
                  -> (Type -> Prim1 Type -> a -> b)
                  -> Translate CompCtx m Expr b
appe1T t f = translate $ \c expr -> case expr of
                      AppE1 ty p e -> f ty p <$> apply t c e                  
                      _            -> fail "not a unary primitive application"
                      
appe1R :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr
appe1R t = appe1T t AppE1
                      
appe2T :: Monad m => Translate CompCtx m Expr a1
                  -> Translate CompCtx m Expr a2
                  -> (Type -> Prim2 Type -> a1 -> a2 -> b)
                  -> Translate CompCtx m Expr b
appe2T t1 t2 f = translate $ \c expr -> case expr of
                     AppE2 ty p e1 e2 -> f ty p <$> apply t1 c e1 <*> apply t2 c e2
                     _                -> fail "not a binary primitive application"

appe2R :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr
appe2R t1 t2 = appe2T t1 t2 AppE2
                     
binopT :: Monad m => Translate CompCtx m Expr a1
                  -> Translate CompCtx m Expr a2
                  -> (Type -> Oper -> a1 -> a2 -> b)
                  -> Translate CompCtx m Expr b
binopT t1 t2 f = translate $ \c expr -> case expr of
                     BinOp ty op e1 e2 -> f ty op <$> apply t1 c e1 <*> apply t2 c e2
                     _                 -> fail "not a binary operator application"

binopR :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr
binopR t1 t2 = binopT t1 t2 BinOp
                     
lamT :: Monad m => Translate CompCtx m Expr a
                -> (Type -> Ident -> a -> b)
                -> Translate CompCtx m Expr b
lamT t f = translate $ \c expr -> case expr of
                     Lam ty n e -> f ty n <$> apply t (bindVar n (domainT ty) c) e
                     _          -> fail "not a lambda"
                     
lamR :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Expr
lamR t = lamT t Lam
                     
ifT :: Monad m => Translate CompCtx m Expr a1
               -> Translate CompCtx m Expr a2
               -> Translate CompCtx m Expr a3
               -> (Type -> a1 -> a2 -> a3 -> b)
               -> Translate CompCtx m Expr b
ifT t1 t2 t3 f = translate $ \c expr -> case expr of
                    If ty e1 e2 e3 -> f ty <$> apply t1 c e1               
                                           <*> apply t2 c e2
                                           <*> apply t3 c e3
                    _              -> fail "not an if expression"
                    
ifR :: Monad m => Rewrite CompCtx m Expr
               -> Rewrite CompCtx m Expr
               -> Rewrite CompCtx m Expr
               -> Rewrite CompCtx m Expr
ifR t1 t2 t3 = ifT t1 t2 t3 If               
                    
litT :: Monad m => (Type -> Val -> b) -> Translate CompCtx m Expr b
litT f = contextfreeT $ \expr -> case expr of
                    Lit ty v -> return $ f ty v
                    _          -> fail "not a constant"
                    
litR :: Monad m => Rewrite CompCtx m Expr
litR = litT Lit
                    
varT :: Monad m => (Type -> Ident -> b) -> Translate CompCtx m Expr b
varT f = contextfreeT $ \expr -> case expr of
                    Var ty n -> return $ f ty n
                    _        -> fail "not a variable"
                    
varR :: Monad m => Rewrite CompCtx m Expr
varR = varT Var

compT :: Monad m => Translate CompCtx m Expr a1
                 -> Translate CompCtx m (NL Qual) a2
                 -> (Type -> a1 -> a2 -> b)
                 -> Translate CompCtx m Expr b
compT t1 t2 f = translate $ \ctx expr -> case expr of
                    Comp ty e qs -> f ty <$> apply t1 (F.foldl' bindQual ctx qs) e 
                                         <*> apply t2 ctx qs
                    _            -> fail "not a comprehension"
                    
compR :: Monad m => Rewrite CompCtx m Expr
                 -> Rewrite CompCtx m (NL Qual)
                 -> Rewrite CompCtx m Expr
compR t1 t2 = compT t1 t2 Comp                 

--------------------------------------------------------------------------------
-- Congruence combinators for qualifiers

bindQualT :: Monad m => Translate CompCtx m Expr a 
                     -> (Ident -> a -> b) 
                     -> Translate CompCtx m Qual b
bindQualT t f = translate $ \ctx expr -> case expr of
                BindQ n e -> f n <$> apply t ctx e
                _         -> fail "not a generator"
                
bindQualR :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Qual
bindQualR t = bindQualT t BindQ

guardQualT :: Monad m => Translate CompCtx m Expr a 
                      -> (a -> b) 
                      -> Translate CompCtx m Qual b
guardQualT t f = translate $ \ctx expr -> case expr of
                GuardQ e -> f <$> apply t ctx e
                _        -> fail "not a guard"
                
guardQualR :: Monad m => Rewrite CompCtx m Expr -> Rewrite CompCtx m Qual
guardQualR t = guardQualT t GuardQ

--------------------------------------------------------------------------------
-- Congruence combinator for a qualifier list

qualsT :: Monad m => Translate CompCtx m Qual a1
                  -> Translate CompCtx m (NL Qual) a2
                  -> (a1 -> a2 -> b) 
                  -> Translate CompCtx m (NL Qual) b
qualsT t1 t2 f = translate $ \ctx quals -> case quals of
                   q :* qs -> f <$> apply t1 ctx q <*> apply t2 (bindQual ctx q) qs
                   S _     -> fail "not a nonempty cons"
                   
qualsR :: Monad m => Rewrite CompCtx m Qual
                  -> Rewrite CompCtx m (NL Qual)
                  -> Rewrite CompCtx m (NL Qual)
qualsR t1 t2 = qualsT t1 t2 (:*)                  

                   
qualsemptyT :: Monad m => Translate CompCtx m Qual a
                       -> (a -> b)
                       -> Translate CompCtx m (NL Qual) b
qualsemptyT t f = translate $ \ctx quals -> case quals of
                      S q -> f <$> apply t ctx q
                      _   -> fail "not a nonempty singleton"
                      
qualsemptyR :: Monad m => Rewrite CompCtx m Qual
                       -> Rewrite CompCtx m (NL Qual)
qualsemptyR t = qualsemptyT t S                       

--------------------------------------------------------------------------------
       
-- | The sum type of *nodes* considered for KURE traversals
data CL = ExprCL Expr
        | QualCL Qual
        | QualsCL (NL Qual)
        
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

        allRqual = bindQualR (extractR r) <+ guardQualR (extractR r)

        allRexpr = varR <+ litR <+ tableR
                   <+ ifR (extractR r) (extractR r) (extractR r)
                   <+ appR (extractR r) (extractR r)
                   <+ appe1R (extractR r)
                   <+ appe2R (extractR r) (extractR r)
                   <+ binopR (extractR r) (extractR r)
                   <+ lamR (extractR r)
                   <+ compR (extractR r) (extractR r)
    

--------------------------------------------------------------------------------
-- I find it annoying that Applicative is not a superclass of Monad.

(<$>) :: Monad m => (a -> b) -> m a -> m b
(<$>) = liftM
{-# INLINE (<$>) #-}

(<*>) :: Monad m => m (a -> b) -> m a -> m b
(<*>) = ap
{-# INLINE (<*>) #-}

