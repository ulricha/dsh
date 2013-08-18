{-# LANGUAGE MultiParamTypeClasses #-}

-- | Infrastructure for KURE-based rewrites on CL expressions
   
module Database.DSH.CL.KURE where
       
import Control.Monad
import qualified Data.Map as M

import Language.KURE
       
import Database.DSH.Common.Data.Type
import Database.DSH.Common.Data.Expr
import Database.DSH.CL.Lang

--------------------------------------------------------------------------------
-- FIXME to be defined
-- | The context for KURE-based CL rewrites
data CompC = CompC { compBindings :: M.Map Ident Type }

-- | Record a variable binding in the context
bindVar :: Ident -> Type -> CompC -> CompC
bindVar n ty c = undefined

--------------------------------------------------------------------------------
-- Congruence combinators for CL nodes

tableT :: Monad m => (Type -> String -> [Column] -> [Key] -> b)
                  -> Translate CompC m Expr b
tableT f = contextfreeT $ \expr -> case expr of
                      Table ty n cs ks -> return $ f ty n cs ks
                      _                -> fail "not a table node"
                                       
appT :: Monad m => Translate CompC m Expr a1
                -> Translate CompC m Expr a2
                -> (Type -> a1 -> a2 -> b)
                -> Translate CompC m Expr b
appT t1 t2 f = translate $ \c expr -> case expr of
                      App ty e1 e2 -> f ty <$> apply t1 c e1 <*> apply t2 c e2
                      _            -> fail "not an application node"
                      
appe1T :: Monad m => Translate CompC m Expr a
                  -> (Type -> Prim1 Type -> a -> b)
                  -> Translate CompC m Expr b
appe1T t f = translate $ \c expr -> case expr of
                      AppE1 ty p e -> f ty p <$> apply t c e                  
                      _            -> fail "not a unary primitive application"
                      
appe2T :: Monad m => Translate CompC m Expr a1
                  -> Translate CompC m Expr a2
                  -> (Type -> Prim2 Type -> a1 -> a2 -> b)
                  -> Translate CompC m Expr b
appe2T t1 t2 f = translate $ \c expr -> case expr of
                     AppE2 ty p e1 e2 -> f ty p <$> apply t1 c e1 <*> apply t2 c e2
                     _                -> fail "not a binary primitive application"

--------------------------------------------------------------------------------
       
-- | The sum type of *nodes* considered for KURE traversals
data CL = ExprCL Expr
        | ExprQual Qualifier
        
instance Injection Expr CL where
    inject                = ExprCL
    
    project (ExprCL expr) = Just expr
    project _             = Nothing

instance Injection Qualifier CL where
    inject               = ExprQual        
    
    project (ExprQual q) = Just q
    project _            = Nothing
    
instance Walker CompC CL where
    allR = undefined
    

--------------------------------------------------------------------------------
-- I find it annoying that Applicative is not a superclass of Monad.

(<$>) :: Monad m => (a -> b) -> m a -> m b
(<$>) = liftM
{-# INLINE (<$>) #-}

(<*>) :: Monad m => m (a -> b) -> m a -> m b
(<*>) = ap
{-# INLINE (<*>) #-}

