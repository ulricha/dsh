{-# Language ScopedTypeVariables #-}

module Ferry.Data where
  
data Exp =
    VarE String
  | UnitE
  | IntE Int
  | BoolE Bool
  | CharE Char
  | TupleE [Exp]
  | ListE [Exp]
  | FuncE (Exp -> Exp)
  | AppE Exp Exp
  | TableE String Type

data Type =
    UnitT
  | IntT
  | BoolT
  | CharT
  | TupleT [Type]
  | ListT Type

data Q a = Q Exp

forget :: Q a -> Exp
forget (Q a) = a

class Reify a where
  reify :: a -> Type
  
instance Reify () where
  reify _ = UnitT
  
instance Reify Int where
  reify _ = IntT
  
instance Reify Bool where
  reify _ = BoolT
  
instance Reify Char where
  reify _ = CharT

instance (Reify a,Reify b) => Reify (a,b) where
  reify _ = TupleT [reify (undefined :: a), reify (undefined :: b)]

instance (Reify a,Reify b,Reify c) => Reify (a,b,c) where
  reify _ = TupleT [reify (undefined :: a), reify (undefined :: b), reify (undefined :: b)]

instance (Reify a) => Reify [a] where
  reify _ = ListT (reify (undefined :: a))
  
  
class BasicType a where
  
instance BasicType () where
instance BasicType Int where
instance BasicType Bool where
instance BasicType Char where