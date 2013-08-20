{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs          #-}

-- | Infrastructure for KURE-based rewrites on CL expressions
   
module Database.DSH.CL.KURE
    (
      -- * The KURE context
      CompC
      -- * Congruence combinators
    , tableT, appT, appe1T, appe2T, binopT, lamT, ifT, litT, varT, compT
    ) where
    
       
import           Control.Monad
import           Data.List
import qualified Data.Map as M

import           Language.KURE
       
import           Database.DSH.Common.Data.Op
import           Database.DSH.Common.Data.Val
import           Database.DSH.Common.Data.Type
import           Database.DSH.Common.Data.Expr
import           Database.DSH.CL.Lang

--------------------------------------------------------------------------------

-- | The context for KURE-based CL rewrites
data CompC = CompC { cl_bindings :: M.Map Ident Type }

-- | Record a variable binding in the context
bindVar :: Ident -> Type -> CompC -> CompC
bindVar n ty ctx = ctx { cl_bindings = M.insert n ty (cl_bindings ctx) }

-- | If the qualifier represents a generator, bind the variable in the context.
bindQual :: CompC -> Qual -> CompC
bindQual ctx (BindQ n e) = bindVar n (elemT $ typeOf e) ctx
bindQual ctx _           = ctx

--------------------------------------------------------------------------------
-- Congruence combinators for CL expressions

tableT :: Monad m => (Type -> String -> [Column] -> [Key] -> b)
                  -> Translate CompC m Expr b
tableT f = contextfreeT $ \expr -> case expr of
                      Table ty n cs ks -> return $ f ty n cs ks
                      _                -> fail "not a table node"
                      
tableR :: Monad m => Rewrite CompC m Expr
tableR = tableT Table
                                       
appT :: Monad m => Translate CompC m Expr a1
                -> Translate CompC m Expr a2
                -> (Type -> a1 -> a2 -> b)
                -> Translate CompC m Expr b
appT t1 t2 f = translate $ \c expr -> case expr of
                      App ty e1 e2 -> f ty <$> apply t1 c e1 <*> apply t2 c e2
                      _            -> fail "not an application node"
                      
appR :: Monad m => Rewrite CompC m Expr -> Rewrite CompC m Expr -> Rewrite CompC m Expr
appR t1 t2 = appT t1 t2 App
                      
appe1T :: Monad m => Translate CompC m Expr a
                  -> (Type -> Prim1 Type -> a -> b)
                  -> Translate CompC m Expr b
appe1T t f = translate $ \c expr -> case expr of
                      AppE1 ty p e -> f ty p <$> apply t c e                  
                      _            -> fail "not a unary primitive application"
                      
appe1R :: Monad m => Rewrite CompC m Expr -> Rewrite CompC m Expr
appe1R t = appe1T t AppE1
                      
appe2T :: Monad m => Translate CompC m Expr a1
                  -> Translate CompC m Expr a2
                  -> (Type -> Prim2 Type -> a1 -> a2 -> b)
                  -> Translate CompC m Expr b
appe2T t1 t2 f = translate $ \c expr -> case expr of
                     AppE2 ty p e1 e2 -> f ty p <$> apply t1 c e1 <*> apply t2 c e2
                     _                -> fail "not a binary primitive application"

appe2R :: Monad m => Rewrite CompC m Expr -> Rewrite CompC m Expr -> Rewrite CompC m Expr
appe2R t1 t2 = appe2T t1 t2 AppE2
                     
binopT :: Monad m => Translate CompC m Expr a1
                  -> Translate CompC m Expr a2
                  -> (Type -> Oper -> a1 -> a2 -> b)
                  -> Translate CompC m Expr b
binopT t1 t2 f = translate $ \c expr -> case expr of
                     BinOp ty op e1 e2 -> f ty op <$> apply t1 c e1 <*> apply t2 c e2
                     _                 -> fail "not a binary operator application"

binopR :: Monad m => Rewrite CompC m Expr -> Rewrite CompC m Expr -> Rewrite CompC m Expr
binopR t1 t2 = binopT t1 t2 BinOp
                     
lamT :: Monad m => Translate CompC m Expr a
                -> (Type -> Ident -> a -> b)
                -> Translate CompC m Expr b
lamT t f = translate $ \c expr -> case expr of
                     Lam ty n e -> f ty n <$> apply t (bindVar n (domainT ty) c) e
                     _          -> fail "not a lambda"
                     
lamR :: Monad m => Rewrite CompC m Expr -> Rewrite CompC m Expr
lamR t = lamT t Lam
                     
ifT :: Monad m => Translate CompC m Expr a1
               -> Translate CompC m Expr a2
               -> Translate CompC m Expr a3
               -> (Type -> a1 -> a2 -> a3 -> b)
               -> Translate CompC m Expr b
ifT t1 t2 t3 f = translate $ \c expr -> case expr of
                    If ty e1 e2 e3 -> f ty <$> apply t1 c e1               
                                           <*> apply t2 c e2
                                           <*> apply t3 c e3
                    _              -> fail "not an if expression"
                    
ifR :: Monad m => Rewrite CompC m Expr
               -> Rewrite CompC m Expr
               -> Rewrite CompC m Expr
               -> Rewrite CompC m Expr
ifR t1 t2 t3 = ifT t1 t2 t3 If               
                    
litT :: Monad m => (Type -> Val -> b) -> Translate CompC m Expr b
litT f = contextfreeT $ \expr -> case expr of
                    Lit ty v -> return $ f ty v
                    _          -> fail "not a constant"
                    
litR :: Monad m => Rewrite CompC m Expr
litR = litT Lit
                    
varT :: Monad m => (Type -> Ident -> b) -> Translate CompC m Expr b
varT f = contextfreeT $ \expr -> case expr of
                    Var ty n -> return $ f ty n
                    _        -> fail "not a variable"
                    
varR :: Monad m => Rewrite CompC m Expr
varR = varT Var

compT :: Monad m => Translate CompC m Expr a1
                 -> Translate CompC m Quals a2
                 -> (Type -> a1 -> a2 -> b)
                 -> Translate CompC m Expr b
compT t1 t2 f = translate $ \ctx expr -> case expr of
                    Comp ty e (Quals qs) -> f ty <$> apply t1 (foldl' bindQual ctx qs) e 
                                                 <*> apply t2 ctx (Quals qs)
                    _            -> fail "not a comprehension"
                    
compR :: Monad m => Rewrite CompC m Expr
                 -> Rewrite CompC m Quals
                 -> Rewrite CompC m Expr
compR t1 t2 = compT t1 t2 Comp                 

--------------------------------------------------------------------------------
-- Congruence combinators for qualifiers

bindQualT :: Monad m => Translate CompC m Expr a 
                     -> (Ident -> a -> b) 
                     -> Translate CompC m Qual b
bindQualT t f = translate $ \ctx expr -> case expr of
                BindQ n e -> f n <$> apply t ctx e
                _         -> fail "not a generator"
                
bindQualR :: Monad m => Rewrite CompC m Expr -> Rewrite CompC m Qual
bindQualR t = bindQualT t BindQ

guardQualT :: Monad m => Translate CompC m Expr a 
                      -> (a -> b) 
                      -> Translate CompC m Qual b
guardQualT t f = translate $ \ctx expr -> case expr of
                GuardQ e -> f <$> apply t ctx e
                _        -> fail "not a guard"
                
guardQualR :: Monad m => Rewrite CompC m Expr -> Rewrite CompC m Qual
guardQualR t = guardQualT t GuardQ

--------------------------------------------------------------------------------
-- Congruence combinator for a qualifier list

qualsT :: Monad m => Translate CompC m Qual a 
                  -> ([a] -> b) 
                  -> Translate CompC m Quals b
qualsT t f = translate $ \ctx (Quals qs) -> f <$> reverse <$> snd <$> foldM aux (ctx, []) qs
  where
    aux (ctx, bs) q = do
        b <- apply t ctx q
        return (bindQual ctx q, b : bs)
        
qualsR :: Monad m => Rewrite CompC m Qual -> Rewrite CompC m Quals
qualsR t = qualsT t Quals
                  

--------------------------------------------------------------------------------
       
-- | The sum type of *nodes* considered for KURE traversals
data CL = ExprCL Expr
        | QualCL Qual
        | QualsCL Quals
        
instance Injection Expr CL where
    inject                = ExprCL
    
    project (ExprCL expr) = Just expr
    project _             = Nothing

instance Injection Qual CL where
    inject             = QualCL
    
    project (QualCL q) = Just q
    project _          = Nothing
    
instance Injection Quals CL where
    inject               = QualsCL
    
    project (QualsCL qs) = Just qs
    project _            = Nothing

    
instance Walker CompC CL where
    allR :: forall m. MonadCatch m => Rewrite CompC m CL -> Rewrite CompC m CL
    allR r = promoteR allRexpr <+ promoteR allRqual <+ promoteR allRquals
    
      where
        -- allRquals :: forall m. MonadCatch m => Rewrite CompC m Quals
        allRquals = qualsR (extractR r)
        -- allRqual :: forall m. MonadCatch m => Rewrite CompC m Qual
        allRqual = bindQualR (extractR r) <+ guardQualR (extractR r)

        -- allRexpr :: forall m. MonadCatch m => Rewrite CompC m Expr
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

