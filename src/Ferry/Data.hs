module Ferry.Data where

data Exp =
    VarE String
  | UnitE
  | BoolE Bool
  | CharE Char
  | IntE Int  
  | TupleE Exp Exp [Exp]
  | ListE [Exp]
  | FuncE (Exp -> Exp)
  | AppE Exp Exp
  | TableE String Type

data Norm =
    UnitN
  | BoolN Bool
  | CharN Char
  | IntN Int
  | TupleN Norm Norm [Norm]
  | ListN [Norm]
  deriving (Eq,Ord,Show)

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

normToExp :: Norm -> Exp
normToExp n = case n of
  UnitN -> UnitE
  BoolN  b -> BoolE b 
  CharN c -> CharE c
  IntN i -> IntE i
  TupleN n1 n2 ns -> TupleE (normToExp n1) (normToExp n2) (map normToExp ns)
  ListN ns -> ListE (map normToExp ns)
  