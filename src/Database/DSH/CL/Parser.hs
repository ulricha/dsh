-- | A parser for comprehension language (CL) expressions.
--
-- @
-- t ::= [t] | (t, ..., t) | Int | Double | ...
--
-- e ::= table(n)::t
--     | (f1 e)::t
--     | (f2 e e)::t
--     | (op1 e)::t
--     | (e op2 e)::t
--     | (if e then e else e)::t
--     | l::t
--     | x::t
--     | [ e | qs ]::t
--     | (e, ..., e)::t
--     | (let x = e in e)::t
--
-- qs ::= x <- e, qs | e, qs | x <- e | e
-- @

module Database.DSH.CL.Parser where

import           Control.Applicative
import           Control.Monad
import           Data.List.NonEmpty       (NonEmpty ((:|)))
import qualified Data.List.NonEmpty       as N
import qualified Data.Text                as T

import           Text.Megaparsec
import qualified Text.Megaparsec.Lexer    as Lex

import           Database.DSH.CL.Lang
import qualified Database.DSH.Common.Lang as L
import qualified Database.DSH.Common.Type as T

type CLParser a = Parsec String a

--------------------------------------------------------------------------------
-- Lexer infrastructure

spaceConsumer :: CLParser ()
spaceConsumer = Lex.space (void spaceChar) empty empty

symbol :: String -> CLParser String
symbol = Lex.symbol spaceConsumer

lexeme :: CLParser a -> CLParser a
lexeme = Lex.lexeme spaceConsumer

parens :: CLParser a -> CLParser a
parens = between (symbol "(") (symbol ")")

brackets :: CLParser a -> CLParser a
brackets = between (symbol "[") (symbol "]")

braces :: CLParser a -> CLParser a
braces = between (symbol "{") (symbol "}")

colon :: CLParser ()
colon = void $ symbol ":"

pipe :: CLParser ()
pipe = void $ symbol "|"

comma :: CLParser ()
comma = void $ symbol ","

ident :: CLParser String
ident = lexeme (some alphaNumChar)

kw :: String -> CLParser ()
kw s = void $ lexeme (string s)

sep :: CLParser ()
sep = spaceConsumer

integerLit :: CLParser Int
integerLit = fromIntegral <$> lexeme Lex.integer

boolLit :: CLParser Bool
boolLit = kw "True" *> pure True <|> kw "False" *> pure False

stringLit :: CLParser String
stringLit = char '"' >> manyTill Lex.charLiteral (char '"')

doubleLit :: CLParser Double
doubleLit = lexeme Lex.float

unitLit :: CLParser ()
unitLit = void $ lexeme $ string "()"

--------------------------------------------------------------------------------
-- Parsing helpers

list :: CLParser a -> CLParser [a]
list p = brackets (p `sepBy` comma)

nonEmpty :: CLParser a -> CLParser (N.NonEmpty a)
nonEmpty p = brackets $ do
    x <- p
    void $ comma
    xs <- p `sepBy` comma
    return $ x :| xs

kwConst :: String -> a -> CLParser a
kwConst s c = kw s *> pure c



--------------------------------------------------------------------------------
-- Types

baseType :: CLParser ScalarType
baseType = try (kw "Int" *> pure T.IntT)
           <|> try (kw "Bool" *> pure T.BoolT)
           <|> try (kw "Double" *> pure T.DoubleT)
           <|> try (kw "()" *> pure T.UnitT)
           <|> try (kw "Decimal" *> pure T.DecimalT)
           <|> try (kw "Date" *> pure T.DateT)

typeExpr :: CLParser T.Type
typeExpr = T.ListT <$> brackets typeExpr
           <|> try (T.ScalarT <$> baseType)
           <|> T.TupleT <$> parens (typeExpr `sepBy1` comma)

typeAnnotation :: CLParser Type
typeAnnotation = colon >> colon >> typeExpr

--------------------------------------------------------------------------------
-- Table references

colName :: CLParser L.ColName
colName = L.ColName <$> ident

tableCols :: CLParser (N.NonEmpty L.Column)
tableCols = nonEmpty $ (,) <$> colName <*> baseType

tableKeys :: CLParser (N.NonEmpty L.Key)
tableKeys = nonEmpty $ L.Key <$> nonEmpty colName

baseTableSchema :: CLParser L.BaseTableSchema
baseTableSchema = do
    cols      <- tableCols
    keys      <- tableKeys
    return $ L.BaseTableSchema cols keys L.PossiblyEmpty

tableRef :: CLParser (Type -> Expr)
tableRef = do
    void $ string "table"
    (tabName, schema) <- parens ((,) <$> ident <*> (comma *> baseTableSchema))
    return $ \ty -> Table ty tabName schema

--------------------------------------------------------------------------------
-- Primitive functions:w

prim1 :: CLParser Prim1
prim1 =     try (kw "singleton" *> pure Singleton)
        <|> try (kw "only" *> pure Only)
        <|> try (kw "length" *> pure Length)
        <|> try (kw "concat" *> pure Concat)
        <|> try (kw "null" *> pure Null)
        <|> try (kw "sum" *> pure Sum)
        <|> try (kw "avg" *> pure Only)
        <|> try (kw "minimum" *> pure Minimum)
        <|> try (kw "maximum" *> pure Maximum)
        <|> try (kw "reverse" *> pure Reverse)
        <|> try (kw "and" *> pure And)
        <|> try (kw "or" *> pure Or)
        <|> try (kw "nub" *> pure Nub)
        <|> try (kw "number" *> pure Number)
        <|> try (kw "only" *> pure Only)
        <|> try (kw "sort" *> pure Sort)
        <|> try (kw "group" *> pure Group)

prim2 :: CLParser Prim2
prim2 =     try (kw "append" *> pure Append)
        <|> try (kw "zip" *> pure Zip)



--------------------------------------------------------------------------------
-- Literals

baseLit :: CLParser L.ScalarVal
baseLit =     try (L.DoubleV <$> doubleLit)
          <|> try (L.IntV <$> integerLit)
          <|> try (L.BoolV <$> boolLit)
          <|> try (L.StringV <$> T.pack <$> stringLit)
          <|> try (unitLit *> pure L.UnitV)

literal :: CLParser L.Val
literal = L.ScalarV <$> baseLit

--------------------------------------------------------------------------------
-- Infix operators
binNumOp :: CLParser L.BinNumOp
binNumOp =     try (kwConst "+" L.Add)
           <|> try (kwConst "-" L.Sub)
           <|> try (kwConst "/" L.Div)
           <|> try (kwConst "*" L.Mul)
           <|> try (kwConst "%" L.Mod)

binRelOp :: CLParser L.BinRelOp
binRelOp =     try (kwConst "==" L.Eq)
           <|> try (kwConst ">" L.Gt)
           <|> try (kwConst ">=" L.GtE)
           <|> try (kwConst "<" L.Lt)
           <|> try (kwConst "<=" L.LtE)
           <|> try (kwConst "!=" L.NEq)

infixOp :: CLParser L.ScalarBinOp
infixOp = L.SBNumOp <$> binNumOp <|> L.SBRelOp <$> binRelOp

--------------------------------------------------------------------------------
-- Prefix operators

prefixNumOp :: CLParser L.UnNumOp
prefixNumOp = kwConst "sin" L.Sin

prefixOp :: CLParser L.ScalarUnOp
prefixOp = L.SUNumOp <$> prefixNumOp

--------------------------------------------------------------------------------
-- Parsing of expressions

app1 :: CLParser (Type -> Expr)
app1 = (\p e t -> AppE1 t p e) <$> prim1 <*> (sep *> typedExpr)

app2 :: CLParser (Type -> Expr)
app2 = (\p e1 e2 t -> AppE2 t p e1 e2) <$> prim2 <*> (sep *> typedExpr) <*> (sep *> typedExpr)

infixApp :: CLParser (Type -> Expr)
infixApp = (\e1 op e2 t -> BinOp t op e1 e2) <$> typedExpr <*> infixOp <*> typedExpr

prefixApp :: CLParser (Type -> Expr)
prefixApp = (\op e t -> UnOp t op e) <$> prefixOp <*> typedExpr

ifExpr :: CLParser (Type -> Expr)
ifExpr = do
    kw "if"
    condExpr <- typedExpr
    kw "then"
    thenExpr <- typedExpr
    kw "else"
    elseExpr <- typedExpr
    return $ \ty -> If ty condExpr thenExpr elseExpr

expr :: CLParser (Type -> Expr)
expr = try app1 <|> try app2 <|> try infixApp <|> try prefixApp <|> try ifExpr

qualifier :: CLParser Qual
qualifier = try (BindQ <$> ident <*> (symbol "<-" *> typedExpr))
            <|> try (GuardQ <$> typedExpr)

comprehension :: CLParser (Type -> Expr)
comprehension = brackets $ do
    headExpr <- typedExpr
    pipe
    quals <- qualifier `sepBy1` comma
    case quals of
        []     -> mzero
        (q:qs) -> return $ \ty -> Comp ty headExpr (fromListSafe q qs)

letExpr :: CLParser (Type -> Expr)
letExpr = do
    kw "let"
    x         <- ident
    void $ symbol "="
    boundExpr <- typedExpr
    kw "in"
    inExpr    <- typedExpr
    return $ \ty -> Let ty x boundExpr inExpr

tupleExpr :: CLParser (Type -> Expr)
tupleExpr = (\es ty -> MkTuple ty es) <$> (parens $ typedExpr `sepBy1` comma)

annotatedExpr :: CLParser Expr
annotatedExpr = do
    exprConst <- parens expr
    ty        <- typeAnnotation
    return $ exprConst ty

typedExpr :: CLParser Expr
typedExpr =     try (tableRef <*> typeAnnotation)
            <|> try annotatedExpr
            <|> try ((\e t -> Lit t e) <$> literal <*> typeAnnotation)
            <|> try ((\n t -> Var t n) <$> ident <*> typeAnnotation)
            <|> try (comprehension <*> typeAnnotation)
            <|> try (tupleExpr <*> typeAnnotation)
            <|> try (letExpr <*> typeAnnotation)

parseCL :: String -> Either String Expr
parseCL inp = case runParser typedExpr "" inp of
    Left err -> Left $ show err
    Right e  -> Right e
