module Ferry.Data where

data Exp =
    UnitE
  | BoolE Bool
  | CharE Char
  | IntE Int  
  | TupleE Exp Exp
  | ListE [Exp]
  | VarE String
  | FuncE (Exp -> Exp)
  | AppE Exp Exp
  | TableE String Type

data Norm =
    UnitN
  | BoolN Bool
  | CharN Char
  | IntN Int
  | TupleN Norm Norm
  | ListN [Norm]
  deriving (Eq,Ord,Show)

data Type =
    UnitT
  | IntT
  | BoolT
  | CharT
  | TupleT Type Type
  | ListT Type
  deriving (Eq, Show)

data Q a = Q Exp

forget :: Q a -> Exp
forget (Q a) = a

normToExp :: Norm -> Exp
normToExp n = case n of
  UnitN -> UnitE
  BoolN  b -> BoolE b 
  CharN c -> CharE c
  IntN i -> IntE i
  TupleN n1 n2 -> TupleE (normToExp n1) (normToExp n2)
  ListN ns -> ListE (map normToExp ns)
  
unfoldType :: Type -> [Type]
unfoldType (TupleT t1 t2) = t1 : unfoldType t2
unfoldType t = [t]