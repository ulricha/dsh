{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}

module Database.DSH.NKL.Quote 
  ( nkl
  , ty
  , Var
  , ExprQ(..)
  , TypeQ(..)
  , varName
  , toExprQ
  , fromExprQ
  , typeOf
  , (.->)
  , elemT
  , freeVars
  ) where

import           Control.Monad
import           Data.Functor
                 
import qualified Data.Set as S

import           Data.Data(Data)
import           Data.Generics.Aliases
import           Data.Typeable(Typeable, Typeable1)
import qualified Language.Haskell.TH as TH
import           Language.Haskell.TH.Quote

import           Text.Parsec hiding (Column)
import           Text.Parsec.Language
import qualified Text.Parsec.Token as P
       
import qualified Text.PrettyPrint.HughesPJ as PP
import           Text.PrettyPrint.HughesPJ((<+>), (<>))

import           Database.DSH.Impossible

import           Database.DSH.Common.Data.Op
import           Database.DSH.Common.Data.Val
import qualified Database.DSH.Common.Data.Type as T
import qualified Database.DSH.NKL.Lang as NKL

data Anti = AntiBind String | AntiWild deriving (Show, Data, Typeable)

data Var = VarLit String
         | VarAntiBind String
         | VarAntiWild
         deriving (Eq, Ord, Show, Data, Typeable)
         
type Column = (String, TypeQ)

data ExprQ = Table TypeQ String [Column] [NKL.Key]
           | App TypeQ ExprQ ExprQ
           | AppE1 TypeQ (NKL.Prim1 TypeQ) ExprQ
           | AppE2 TypeQ (NKL.Prim2 TypeQ) ExprQ ExprQ
           | BinOp TypeQ Oper ExprQ ExprQ
           | Lam TypeQ Var ExprQ
           | If TypeQ ExprQ ExprQ ExprQ
           | Const TypeQ Val
           | Var TypeQ Var
           -- Antiquotation node
           | AntiE Anti
           deriving (Data, Typeable)

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
           | AntiT Anti
           deriving (Show, Typeable, Data)
           
deriving instance Typeable NKL.Prim2Op
deriving instance Data NKL.Prim2Op

deriving instance Typeable NKL.Prim1Op
deriving instance Data NKL.Prim1Op
           
deriving instance Typeable1 NKL.Prim2
deriving instance Data t => Data (NKL.Prim2 t)

deriving instance Typeable1 NKL.Prim1
deriving instance Data t => Data (NKL.Prim1 t)
           
--------------------------------------------------------------------------
-- Conversion to and from quotation types

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

toExprQ :: NKL.Expr -> ExprQ
--toExprQ (NKL.Table t n cs ks)    = Table (toTypeQ t) n cs ks
toExprQ (NKL.Table t n cs ks)    = Table (toTypeQ t) n (map (\(x, y) -> (x, toTypeQ y)) cs) ks
toExprQ (NKL.App t e1 e2)        = App (toTypeQ t) (toExprQ e1) (toExprQ e2)
toExprQ (NKL.AppE1 t p e)        = AppE1 (toTypeQ t) (toPrim1Q p) (toExprQ e)
toExprQ (NKL.AppE2 t p e1 e2)    = AppE2 (toTypeQ t) (toPrim2Q p) (toExprQ e1) (toExprQ e2)
toExprQ (NKL.BinOp t o e1 e2)    = BinOp (toTypeQ t) o (toExprQ e1) (toExprQ e2)
toExprQ (NKL.Lam t v e)          = Lam (toTypeQ t) (VarLit v) (toExprQ e)
toExprQ (NKL.If t c thenE elseE) = If (toTypeQ t) (toExprQ c) (toExprQ thenE) (toExprQ elseE)
toExprQ (NKL.Const t v)          = Const (toTypeQ t) v
toExprQ (NKL.Var t v)            = Var (toTypeQ t) (VarLit v)

fromExprQ :: ExprQ -> NKL.Expr
-- fromExprQ (Table t n cs ks)    = NKL.Table (fromTypeQ t) n cs ks
fromExprQ (Table t n cs ks)    = NKL.Table (fromTypeQ t) n (map (\(x, y) -> (x, fromTypeQ y)) cs) ks
fromExprQ (App t e1 e2)        = NKL.App (fromTypeQ t) (fromExprQ e1) (fromExprQ e2)
fromExprQ (AppE1 t p e)        = NKL.AppE1 (fromTypeQ t) (fromPrim1Q p) (fromExprQ e)
fromExprQ (AppE2 t p e1 e2)    = NKL.AppE2 (fromTypeQ t) (fromPrim2Q p) (fromExprQ e1) (fromExprQ e2)
fromExprQ (BinOp t o e1 e2)    = NKL.BinOp (fromTypeQ t) o (fromExprQ e1) (fromExprQ e2)
fromExprQ (Lam t b e)          = NKL.Lam (fromTypeQ t) (varName b) (fromExprQ e)
fromExprQ (If t c thenE elseE) = NKL.If (fromTypeQ t) (fromExprQ c) (fromExprQ thenE) (fromExprQ elseE)
fromExprQ (Const t v)          = NKL.Const (fromTypeQ t) v
fromExprQ (Var t v)            = NKL.Var (fromTypeQ t) (varName v)
fromExprQ (AntiE e)            = error $ show e

varName :: Var -> String
varName (VarLit s)      = s
varName (VarAntiBind _) = $impossible
varName VarAntiWild     = $impossible

fromPrim1Q :: NKL.Prim1 TypeQ -> NKL.Prim1 T.Type
fromPrim1Q (NKL.Prim1 o t) = NKL.Prim1 o (fromTypeQ t)

toPrim1Q :: NKL.Prim1 T.Type -> NKL.Prim1 TypeQ
toPrim1Q (NKL.Prim1 o t) = NKL.Prim1 o (toTypeQ t)

fromPrim2Q :: NKL.Prim2 TypeQ -> NKL.Prim2 T.Type
fromPrim2Q (NKL.Prim2 o t) = NKL.Prim2 o (fromTypeQ t)

toPrim2Q :: NKL.Prim2 T.Type -> NKL.Prim2 TypeQ
toPrim2Q (NKL.Prim2 o t) = NKL.Prim2 o (toTypeQ t)

--------------------------------------------------------------------------
-- Some helper functions on quotable types and expressions, analogous to 
-- those in NKL and Type.

-- | Extract the type annotation from an expression
typeOf :: ExprQ -> TypeQ
typeOf (Table t _ _ _) = t
typeOf (App t _ _)     = t
typeOf (AppE1 t _ _)   = t
typeOf (AppE2 t _ _ _) = t
typeOf (BinOp t _ _ _) = t
typeOf (Lam t _ _)     = t
typeOf (If t _ _ _)    = t
typeOf (Const t _)     = t
typeOf (Var t _)       = t
typeOf (AntiE _)       = $impossible

(.->) :: TypeQ -> TypeQ -> TypeQ
(.->) t1 t2 = FunT t1 t2

elemT :: TypeQ -> TypeQ
elemT (ListT t) = t
elemT _         = $impossible

freeVars :: ExprQ -> S.Set Var
freeVars (Table _ _ _ _)   = S.empty
freeVars (App _ e1 e2)     = freeVars e1 `S.union` freeVars e2
freeVars (AppE1 _ _ e1)    = freeVars e1
freeVars (AppE2 _ _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (Lam _ x e)       = (freeVars e) S.\\ S.singleton x
freeVars (If _ e1 e2 e3)   = freeVars e1 `S.union` freeVars e2 `S.union` freeVars e3
freeVars (BinOp _ _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (Const _ _)       = S.empty
freeVars (Var _ x)         = S.singleton x
freeVars (AntiE _)         = $impossible

instance Show ExprQ where
  show e = PP.render $ pp e
  
pp :: ExprQ -> PP.Doc
pp (Table _ n _ _)    = PP.text "table" <+> PP.text n
pp (App _ e1 e2)      = (PP.parens $ pp e1) <+> (PP.parens $ pp e2)
pp (AppE1 _ p1 e)     = (PP.text $ show p1) <+> (PP.parens $ pp e)
pp (AppE2 _ p1 e1 e2) = (PP.text $ show p1) <+> (PP.parens $ pp e1) <+> (PP.parens $ pp e2)
pp (BinOp _ o e1 e2)  = (PP.parens $ pp e1) <+> (PP.text $ show o) <+> (PP.parens $ pp e2)
pp (Lam _ v e)        = PP.char '\\' <> PP.text (varName v) <+> PP.text "->" <+> pp e
pp (If _ c t e)       = PP.text "if" 
                        <+> pp c 
                        <+> PP.text "then" 
                        <+> (PP.parens $ pp t) 
                        <+> PP.text "else" 
                        <+> (PP.parens $ pp e)
pp (Const _ v)        = PP.text $ show v
pp (Var _ s)          = PP.text $ varName s
pp (AntiE _)          = $impossible

--------------------------------------------------------------------------
-- A parser for NKL expressions and types, including anti-quotation syntax

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
typ = do { void $ char '\''; AntiT <$> AntiBind <$> identifier }
      *<|> do { reservedOp "_"; return (AntiT AntiWild) }
      *<|> do { reserved "nat"; return NatT }
      *<|> do { reserved "int"; return IntT }
      *<|> do { reserved "bool"; return BoolT }
      *<|> do { reserved "double"; return DoubleT }
      *<|> do { reserved "string"; return StringT }
      *<|> do { reserved "unit"; return UnitT }
      *<|> do { i <- identifier; return $ VarT i }
      *<|> try (parens $ do { t1 <- typ
                            ; reservedOp "->"
                            ; t2 <- typ
                            ; return $ FunT t1 t2
                            } )
      *<|> (parens $ do { t1 <- typ
                        ; void comma
                        ; t2 <- typ
                        ; return $ PairT t1 t2
                        } )
      *<|> do { t <- brackets typ; return $ ListT t }
      
prim1s :: [Parse (TypeQ -> NKL.Prim1 TypeQ)]
prim1s = [ reserved "length" >> return (NKL.Prim1 NKL.Length)
         , reserved "not" >> return (NKL.Prim1 NKL.Not)
         , reserved "concat" >> return (NKL.Prim1 NKL.Concat)
         , reserved "sum" >> return (NKL.Prim1 NKL.Sum)
         , reserved "avg" >> return (NKL.Prim1 NKL.Avg)
         , reserved "the" >> return (NKL.Prim1 NKL.The)
         , reserved "fst" >> return (NKL.Prim1 NKL.Fst)
         , reserved "snd" >> return (NKL.Prim1 NKL.Snd)
         , reserved "head" >> return (NKL.Prim1 NKL.Head)
         , reserved "minimum" >> return (NKL.Prim1 NKL.Minimum)
         , reserved "maximum" >> return (NKL.Prim1 NKL.Maximum)
         , reserved "integerToDouble" >> return (NKL.Prim1 NKL.IntegerToDouble)
         , reserved "tail" >> return (NKL.Prim1 NKL.Tail)
         , reserved "reverse" >> return (NKL.Prim1 NKL.Reverse)
         , reserved "and" >> return (NKL.Prim1 NKL.And)
         , reserved "or" >> return (NKL.Prim1 NKL.Or)
         , reserved "init" >> return (NKL.Prim1 NKL.Init)
         , reserved "last" >> return (NKL.Prim1 NKL.Last)
         , reserved "nub" >> return (NKL.Prim1 NKL.Nub)
         ]
      
prim1 :: Parse (NKL.Prim1 TypeQ)
prim1 = do { p <- choice prim1s
           ; reservedOp "::"
           ; t <- typ
           ; return $ p t
           }
           
prim2s :: [Parse (TypeQ -> NKL.Prim2 TypeQ)]
prim2s = [ reserved "map" >> return (NKL.Prim2 NKL.Map)
         , reserved "groupWithKey" >> return (NKL.Prim2 NKL.GroupWithKey)
         , reserved "sortWith" >> return (NKL.Prim2 NKL.SortWith)
         , reserved "pair" >> return (NKL.Prim2 NKL.Pair)
         , reserved "filter" >> return (NKL.Prim2 NKL.Filter)
         , reserved "append" >> return (NKL.Prim2 NKL.Append)
         , reserved "index" >> return (NKL.Prim2 NKL.Index)
         , reserved "zip" >> return (NKL.Prim2 NKL.Zip)
         , reserved "cartProduct" >> return (NKL.Prim2 NKL.CartProduct)
         ]

prim2 :: Parse (NKL.Prim2 TypeQ)
prim2 = do { p <- choice prim2s
           ; reservedOp "::"
           ; t <- typ
           ; return $ p t
           }
           
val :: Parse Val
val = (IntV <$> natural)
      <|> (StringV <$> stringLiteral)
      <|> (DoubleV <$> float)
      <|> (reserved "true" >> return (BoolV True))
      <|> (reserved "false" >> return (BoolV False))
      <|> (reserved "unit" >> return UnitV)
      <|> (ListV <$> (brackets $ commaSep val))
      <|> (parens $ do { v1 <- val
                       ; void comma
                       ; v2 <- val
                       ; return $ PairV v1 v2
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
            
infixr 1 *<|>
(*<|>) :: ParsecT s u m a -> ParsecT s u m a -> ParsecT s u m a
a *<|> b = try a <|> b

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
               ; return $ Var t (VarLit i)
               }
       *<|> do { void $ char '\''
               ; i <- identifier
               ; reservedOp "::"
               ; t <- typ
               ; return $ Var t (VarAntiBind i)
               }
       *<|> do { void $ char '_'
               ; reservedOp "::"
               ; t <- typ
               ; return $ Var t VarAntiWild
               }
       *<|> do { reservedOp "_"; return (AntiE AntiWild) }
       *<|> do { void $ char '\''
               ; i <- identifier
               ; return $ AntiE $ AntiBind i
               }
               
var :: Parse Var
var = do { void $ char '\''; VarAntiBind <$> identifier }
      *<|> do { void $ char '_'; return VarAntiWild }
      *<|> do { VarLit <$> identifier }
      
keys :: Parse [NKL.Key]
keys = brackets $ commaSep $ brackets $ commaSep1 identifier

columns :: Parse [Column]
columns = brackets $ commaSep1 $ parens $ do
  c <- identifier
  void comma 
  t <- typ
  return (c, t)
  

cexpr :: Parse (TypeQ -> ExprQ)
cexpr = do { reserved "table"
           ; n <- identifier
           ; cs <- columns
           ; ks <- keys
           ; return $ \t -> Table t n cs ks
           }
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
        *<|> do { reservedOp "\\"
                ; v <- var
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
                Left e  -> error $ i ++ " " ++ show e
                Right t -> t

--------------------------------------------------------------------------
-- Quasi-Quoting
                
antiExprExp :: ExprQ -> Maybe (TH.Q TH.Exp)
antiExprExp (AntiE (AntiBind s)) = Just $ TH.varE (TH.mkName s)
antiExprExp (AntiE AntiWild)     = error "NKL.Quote: wildcard pattern (expr) used in expression quote"
antiExprExp _                    = Nothing

antiExprPat :: ExprQ -> Maybe (TH.Q TH.Pat)
antiExprPat (AntiE (AntiBind s)) = Just $ TH.varP (TH.mkName s)
antiExprPat (AntiE AntiWild)     = Just TH.wildP
antiExprPat _                    = Nothing

antiTypeExp :: TypeQ -> Maybe (TH.Q TH.Exp)
antiTypeExp (AntiT (AntiBind s)) = Just $ TH.varE (TH.mkName s)
antiTypeExp (AntiT AntiWild)     = error "NKL.Quote: wildcard pattern (type) used in expression quote"
antiTypeExp _                    = Nothing

antiTypePat :: TypeQ -> Maybe (TH.Q TH.Pat)
antiTypePat (AntiT (AntiBind s)) = Just $ TH.varP (TH.mkName s)
antiTypePat (AntiT AntiWild)     = Just TH.wildP
antiTypePat _                    = Nothing

antiVarExp :: Var -> Maybe (TH.Q TH.Exp)
antiVarExp (VarAntiBind s) = Just $ TH.varE (TH.mkName s)
antiVarExp VarAntiWild     = error "NKL.Quote: wildcard pattern (variable) used in expression quote"
antiVarExp (VarLit _)      = Nothing
            
antiVarPat :: Var -> Maybe (TH.Q TH.Pat)
antiVarPat (VarAntiBind s) = Just $ TH.varP (TH.mkName s)
antiVarPat VarAntiWild     = Just TH.wildP
antiVarPat _               = Nothing

quoteExprExp :: String -> TH.ExpQ
quoteExprExp s = dataToExpQ (const Nothing `extQ` antiExprExp
                                           `extQ` antiTypeExp
                                           `extQ` antiVarExp) $ parseExpr s

quoteExprPat :: String -> TH.PatQ
quoteExprPat s = dataToPatQ (const Nothing `extQ` antiExprPat
                                           `extQ` antiTypePat
                                           `extQ` antiVarPat) $ parseExpr s
                                           
quoteTypeExp :: String -> TH.ExpQ
quoteTypeExp s = dataToExpQ (const Nothing `extQ` antiTypeExp) $ parseType s

quoteTypePat :: String -> TH.PatQ
quoteTypePat s = dataToPatQ (const Nothing `extQ` antiTypePat) $ parseType s
                                           
-- | A quasi quoter for the Flattening type language
ty :: QuasiQuoter
ty = QuasiQuoter { quoteExp = quoteTypeExp
                 , quotePat = quoteTypePat
                 , quoteDec = error "Can't use NKL quasiquoter for declarations"
                 , quoteType = error "Can't use NKL quasiquoter for types"
                 }

-- | A quasi quoter for NKL expressions
nkl :: QuasiQuoter
nkl = QuasiQuoter { quoteExp = quoteExprExp
                  , quotePat = quoteExprPat
                  , quoteDec = error "Can't use NKL quasiquoter for declarations"
                  , quoteType = error "Can't use NKL quasiquoter for types"
                  }
