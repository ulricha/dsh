module Language.ParallelLang.Common.Data.Prelude where
    
import Language.ParallelLang.Common.Data.Type

import qualified Data.Map as M

preludeEnv :: TyEnv
preludeEnv v = M.findWithDefault ((tupleConstr emptyTyEnv) v) v $ M.fromList primFuns  

primFuns :: [(String, TypeScheme)]
primFuns = [("+",        Ty $ intT .-> intT .-> intT),
            ("-",        Ty $ intT .-> intT .-> intT),
            ("/",        Ty $ intT .-> intT .-> intT),
            ("*",        Ty $ intT .-> intT .-> intT),
            ("&&",       Ty $ boolT .-> boolT .-> boolT),
            ("||",       Ty $ boolT .-> boolT .-> boolT),
            ("<",        Ty $ intT .-> intT .-> boolT),
            (">",        Ty $ intT .-> intT .-> boolT),
            ("==",        Ty $ intT .-> intT .-> boolT),
            (">=",        Ty $ intT .-> intT .-> boolT),
            ("<=",        Ty $ intT .-> intT .-> boolT),
            (":",        Forall "a" $ Ty $ (Var "a") .-> (listT $ Var "a") .-> (listT $ Var "a")),
            ("not",      Ty $ boolT .-> boolT),
            ("index",    Forall "a" $ Ty $ (listT $ Var "a") .-> intT .-> Var "a"),
            ("length",   Forall "a" $ Ty $ (listT $ Var "a") .-> intT),
            ("dist",     Forall "a" $ Forall "b" $ Ty $ Var "a" .-> listT (Var "b") .-> (listT $ Var "a")),
            ("range",    Ty $ intT .-> intT .-> (listT intT)),
            ("restrict", Forall "a" $ Ty $ listT boolT .-> listT (Var "a") .-> listT (Var "a")),
            ("combine",  Forall "a" $ Ty $ listT boolT .-> listT (Var "a") .-> listT (Var "a") .-> listT (Var "a")),
            ("promote",  Forall "a" $ Forall "b" $ Ty $ Var "a" .-> listT (Var "b") .-> listT (Var "a")),
            ("insert",   Forall "a" $ Ty $ Var "a"), -- insert and extract are not supposed to be used by users
            ("extract",  Forall "a" $ Ty $ Var "a"),
            ("bPermute", Forall "a" $ Ty $ listT (Var "a") .-> listT intT .-> listT (Var "a"))] 
            
tupleConstr :: (String -> TypeScheme) -> String -> TypeScheme
tupleConstr g v = case v of
                    ('(':vs) -> if (dropWhile (\x -> x == ',') vs) == ")"
                                    then genTupleScheme $ (length v) - 1
                                    else g v
                    _ -> g v
                    
genTupleScheme :: Int -> TypeScheme
genTupleScheme i = let vs = ['a' : show v | v <- [1..i]]
                       t = TyC "tuple" [Var v | v <- vs]
                    in foldr (\v ty -> Forall v ty) (Ty $ foldr (\v ty -> Var v .-> ty) t vs) vs