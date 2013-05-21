{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Flattening.NKL.Quote where

import           Control.Monad
import           Data.Functor
import           Language.Haskell.TH.Quote
import           Text.Parsec
import           Text.Parsec.Language
import qualified Text.Parsec.Token as P

import           Database.DSH.Impossible

import           Database.DSH.Flattening.Common.Data.Op
import           Database.DSH.Flattening.Common.Data.Val
import qualified Database.DSH.Flattening.Common.Data.Type as T
import           Database.DSH.Flattening.Common.Data.Val(Val())
import qualified Database.DSH.Flattening.NKL.Data.NKL as NKL

data ExprQ = Table TypeQ String [NKL.Column] [NKL.Key]
           | App TypeQ ExprQ ExprQ
           | AppE1 TypeQ (NKL.Prim1 TypeQ) ExprQ
           | AppE2 TypeQ (NKL.Prim2 TypeQ) ExprQ ExprQ
           | BinOp TypeQ Oper ExprQ ExprQ
           | Lam TypeQ String ExprQ
           | If TypeQ ExprQ ExprQ ExprQ
           | Const TypeQ Val
           | Var TypeQ String
           -- Antiquotation node
           | AntiE String
           deriving (Show)
           
data TypeQ = FunT TypeQ TypeQ
           | NatT 
           | IntT 
           | BoolT 
           | DoubleT
           | StringT 
           | UnitT 
           | VarT String
           | PairT TypeQ TypeQ 
           | ListT TypeQ
           -- Antiquotation node
           | AntiT String
           deriving (Show)
           
{-
-- FIXME really necessary?
toTypeQ :: T.Type -> TypeQ
toTypeQ (T.FunT t1 t2)  = FunT (toTypeQ t1) (toTypeQ t2)
toTypeQ T.NatT          = NatT
toTypeQ T.IntT          = IntT
toTypeQ T.BoolT         = BoolT
toTypeQ T.DoubleT       = DoubleT
toTypeQ T.StringT       = StringT
toTypeQ T.UnitT         = UnitT
toTypeQ (T.VarT v)      = VarT v
toTypeQ (T.PairT t1 t2) = PairT (toTypeQ t1) (toTypeQ t2)
toTypeQ (T.ListT t)     = ListT (toTypeQ t)
-}

fromTypeQ :: TypeQ -> T.Type
fromTypeQ (FunT t1 t2)  = T.FunT (fromTypeQ t1) (fromTypeQ t2)
fromTypeQ NatT          = T.NatT
fromTypeQ IntT          = T.IntT
fromTypeQ BoolT         = T.BoolT
fromTypeQ DoubleT       = T.DoubleT
fromTypeQ StringT       = T.StringT
fromTypeQ UnitT         = T.UnitT
fromTypeQ (VarT v)      = T.VarT v
fromTypeQ (PairT t1 t2) = T.PairT (fromTypeQ t1) (fromTypeQ t2)
fromTypeQ (ListT t)     = T.ListT (fromTypeQ t)
fromTypeQ (AntiT _)     = $impossible

{-
-- FIXME really necessary?         
toExprQ :: NKL.Expr -> ExprQ
toExprQ (NKL.Table t n cs ks)    = Table (toTypeQ t) n cs ks
toExprQ (NKL.App t e1 e2)        = App (toTypeQ t) (toExprQ e1) (toExprQ e2)
toExprQ (NKL.AppE1 t p e)        = AppE1 (toTypeQ t) p (toExprQ e)
toExprQ (NKL.AppE2 t p e1 e2)    = AppE2 (toTypeQ t) p (toExprQ e1) (toExprQ e2)
toExprQ (NKL.BinOp t o e1 e2)    = BinOp (toTypeQ t) o (toExprQ e1) (toExprQ e2)
toExprQ (NKL.Lam t v e)          = Lam (toTypeQ t) v (toExprQ e)
toExprQ (NKL.If t c thenE elseE) = If (toTypeQ t) (toExprQ c) (toExprQ thenE) (toExprQ elseE)
toExprQ (NKL.Const t v)          = Const (toTypeQ t) v
toExprQ (NKL.Var t v)            = Var (toTypeQ t) v
-}

fromExprQ :: ExprQ -> NKL.Expr
fromExprQ (Table t n cs ks)    = NKL.Table (fromTypeQ t) n cs ks
fromExprQ (App t e1 e2)        = NKL.App (fromTypeQ t) (fromExprQ e1) (fromExprQ e2)
fromExprQ (AppE1 t p e)        = NKL.AppE1 (fromTypeQ t) (fromPrim1Q p) (fromExprQ e)
fromExprQ (AppE2 t p e1 e2)    = NKL.AppE2 (fromTypeQ t) (fromPrim2Q p) (fromExprQ e1) (fromExprQ e2)
fromExprQ (BinOp t o e1 e2)    = NKL.BinOp (fromTypeQ t) o (fromExprQ e1) (fromExprQ e2)
fromExprQ (Lam t v e)          = NKL.Lam (fromTypeQ t) v (fromExprQ e)
fromExprQ (If t c thenE elseE) = NKL.If (fromTypeQ t) (fromExprQ c) (fromExprQ thenE) (fromExprQ elseE)
fromExprQ (Const t v)          = NKL.Const (fromTypeQ t) v
fromExprQ (Var t v)            = NKL.Var (fromTypeQ t) v
fromExprQ (AntiE _)            = $impossible
          
fromPrim1Q :: NKL.Prim1 TypeQ -> NKL.Prim1 T.Type
fromPrim1Q = undefined

fromPrim2Q :: NKL.Prim2 TypeQ -> NKL.Prim2 T.Type
fromPrim2Q = undefined

{-
gExpr -> (CExpr)::Type
      | Const::Type
      | Var::Type
      
CExpr -> table Id [Id] [Id]
       | Expr Expr
       | Prim1 Expr
       | Prim2 Expr Expr
       | Expr Op Expr
       | \Id -> Expr
       | if Expr then Expr else Expr
       
Id -> ...

Prim1 -> ...

Prim2 -> ...

Op -> ...

Type -> (Type -> Type)
      | nat
      | int
      | bool
      | double
      | string
      | unit
      | Id
      | (Type, Type)
      | [Type]

-}

type Parse = Parsec String ()

lexer :: P.TokenParser ()
lexer = P.makeTokenParser haskellDef

reserved :: String -> Parse ()
reserved = P.reserved lexer

parens :: Parse a -> Parse a
parens = P.parens lexer

reservedOp :: String -> Parse ()
reservedOp = P.reservedOp lexer

comma :: Parse String
comma = P.comma lexer

identifier :: Parse String
identifier = P.identifier lexer

brackets :: Parse a -> Parse a
brackets = P.brackets lexer

commaSep :: Parse a -> Parse [a]
commaSep = P.commaSep lexer

float :: Parse Double
float = P.float lexer

natural :: Parse Int
natural = fromInteger <$> P.natural lexer

stringLiteral :: Parse String
stringLiteral = P.stringLiteral lexer

commaSep1 :: Parse a -> Parse [a]
commaSep1 = P.commaSep1 lexer


typ :: Parse TypeQ
typ = do { reserved "nat"; return NatT }
      <|> do { reserved "int"; return IntT }
      <|> do { reserved "bool"; return BoolT }
      <|> do { reserved "double"; return DoubleT }
      <|> do { reserved "string"; return StringT }
      <|> do { reserved "unit"; return UnitT }
      <|> do { i <- identifier; return $ VarT i }
      <|> try (parens $ do { t1 <- typ
                           ; reservedOp "->"
                           ; t2 <- typ
                           ; return $ FunT t1 t2
                           } )
      <|> (parens $ do { t1 <- typ
                       ; void comma
                       ; t2 <- typ
                       ; return $ PairT t1 t2
                       } )
      <|> do { t <- brackets typ; return $ ListT t }
      
prim1s :: [Parse (TypeQ -> NKL.Prim1 TypeQ)]
prim1s = [ reserved "length" >> return NKL.Length
         , reserved "not" >> return NKL.Not
         , reserved "concat" >> return NKL.Concat
         , reserved "sum" >> return NKL.Sum
         , reserved "avg" >> return NKL.Avg
         , reserved "the" >> return NKL.The
         , reserved "fst" >> return NKL.Fst
         , reserved "snd" >> return NKL.Snd
         , reserved "head" >> return NKL.Head
         , reserved "minimum" >> return NKL.Minimum
         , reserved "maximum" >> return NKL.Maximum
         , reserved "integerToDouble" >> return NKL.IntegerToDouble
         , reserved "tail" >> return NKL.Tail
         , reserved "reverse" >> return NKL.Reverse
         , reserved "and" >> return NKL.And
         , reserved "or" >> return NKL.Or
         , reserved "init" >> return NKL.Init
         , reserved "last" >> return NKL.Last
         , reserved "nub" >> return NKL.Nub
         ]
      
prim1 :: Parse (NKL.Prim1 TypeQ)
prim1 = do { p <- choice prim1s
           ; reservedOp "::"
           ; t <- typ
           ; return $ p t
           }
           
prim2s :: [Parse (TypeQ -> NKL.Prim2 TypeQ)]
prim2s = [ reserved "map" >> return NKL.Map
         , reserved "groupWithKey" >> return NKL.GroupWithKey
         , reserved "sortWith" >> return NKL.SortWith
         , reserved "pair" >> return NKL.Pair
         , reserved "filter" >> return NKL.Filter
         , reserved "append" >> return NKL.Append
         , reserved "index" >> return NKL.Index
         , reserved "take" >> return NKL.Take
         , reserved "drop" >> return NKL.Drop
         , reserved "zip" >> return NKL.Zip
         , reserved "takeWhile" >> return NKL.TakeWhile
         , reserved "dropWhile" >> return NKL.DropWhile
         , reserved "cartProduct" >> return NKL.CartProduct
         ]

prim2 :: Parse (NKL.Prim2 TypeQ)
prim2 = do { p <- choice prim2s
           ; reservedOp "::"
           ; t <- typ
           ; return $ p t
           }
           
val :: Parse Val
val = (Int <$> natural)
      <|> (String <$> stringLiteral)
      <|> (Double <$> float)
      <|> (reserved "unit" >> return Unit)
      <|> (List <$> (brackets $ commaSep val))
      <|> (parens $ do { v1 <- val
                       ; void comma
                       ; v2 <- val
                       ; return $ Pair v1 v2
                       } )
                       
op :: Parse Oper
op = choice [ reservedOp "+" >> return Add
            , reservedOp "-" >> return Sub
            , reservedOp "/" >> return Div
            , reservedOp "*" >> return Mul
            , reservedOp "%" >> return Mod
            , reservedOp "==" >> return Eq
            , reservedOp ">" >> return Gt
            , reservedOp ">=" >> return GtE
            , reservedOp "<" >> return Lt
            , reservedOp "<=" >> return LtE
            , reservedOp ":" >> return Cons
            , reservedOp "&&" >> return Conj
            , reservedOp "||" >> return Disj
            , reservedOp "LIKE" >> return Like
            ]
            
{-
keys :: Parse [NKL.Key]
keys = reserved "keys"

columns :: Parse [NKL.Column]
columns = reserved "cols"
-}

expr :: Parse ExprQ
expr = do { v <- val
          ; reservedOp "::"
          ; t <- typ
          ; return $ Const t v
          }
       *<|> do { e <- parens cexpr
               ; reservedOp "::"
               ; t <- typ
               ; return $ e t
               }
       *<|> do { i <- identifier
               ; reservedOp "::"
               ; t <- typ
               ; return $ Var t i
               }
              
infixr 1 *<|>
a *<|> b = try a <|> b

cexpr :: Parse (TypeQ -> ExprQ)
cexpr = do { reserved "table" >> undefined }
      {-
           ; n <- identifier
           ; cs <- columns
           ; ks <- keys
           ; return $ \t -> Table t n cs ks
           }
       -}
        *<|> do { e1 <- expr
                ; o <- op
                ; e2 <- expr
                ; return $ \t -> BinOp t o e1 e2
                }
        *<|> do { p <- prim1
                ; e <- expr
                ; return $ \t -> AppE1 t p e
                }
        *<|> do { p <- prim2
                ; e1 <- expr
                ; e2 <- expr
                ; return $ \t -> AppE2 t p e1 e2
                }
        *<|> do { e1 <- expr
                ; e2 <- expr
                ; return $ \t -> App t e1 e2
                }
        *<|> do { reserved "if"
                ; condE <- expr
                ; reserved "then"
                ; thenE <- expr
                ; reserved "else"
                ; elseE <- expr
                ; return $ \t -> If t condE thenE elseE
                }
        *<|> do { reservedOp "|"
                ; v <- identifier
                ; reservedOp "->"
                ; e <- expr
                ; return $ \t -> Lam t v e
                }
            
       
parseType :: String -> TypeQ
parseType i = case parse typ "" i of
                Left e  -> error $ show e
                Right t -> t

parseExpr :: String -> ExprQ
parseExpr i = case parse expr "" i of
                Left e  -> error $ show e
                Right t -> t
                
parseVal :: String -> Val
parseVal i = case parse val "" i of
                Left e  -> error $ show e
                Right t -> t
