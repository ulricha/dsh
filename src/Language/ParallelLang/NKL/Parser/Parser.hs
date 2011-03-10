{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.NKL.Parser.Parser(parseProgram) where

import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec

import Control.Applicative hiding ((<|>), Const, many)
import Language.ParallelLang.NKL.Parser.Config

import Language.ParallelLang.NKL.Data.UntypedNKL
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Op
import qualified Language.ParallelLang.Common.Data.Type as T

parseProgram :: String -> [Char] -> ([Expr], Expr)
parseProgram file src = case parse parseInput file src of
                            Left e -> error $ show e
                            Right r -> r

parseInput :: Parser ([Expr], Expr)
parseInput = whiteSpace *> program <* eof

{-
Parsing a program. Structure of a program:

let
    function1 ....
    functionn ....
in
    expr
|
expr
-}

program :: Parser ([Expr], Expr)
program = choice [try $ (\fns e -> (fns, e)) <$ reserved "let" <*> many1 pFunction <* reserved "in" <*> pExpr
                 ,(\e -> ([], e)) <$> pExpr]

{-
Parse a function. A function has the form:
name :: type
name arg1 ... argn = 
  return expr
-}

pFunction :: Parser Expr
pFunction = try functionWithType <|> pFunctionNoType

pFunctionNoType :: Parser Expr
pFunctionNoType = Fn <$> identifier <*> (option 0 (fromInteger <$ symbol "^" <*> natural)) <*> many identifier <* reservedOp "=" 
                        <*> pExpr <*> pure Nothing

functionWithType :: Parser Expr
functionWithType = do
                    n1 <- identifier
                    symbol "::" 
                    t <- parseType
                    (Fn n2 l args e _) <- pFunctionNoType
                    if n1 == n2
                        then return $ Fn n1 l args e (Just t) 
                        else error $ "Found type for function: " ++ n1 ++ "\nBut the declaration that followed was: " ++ n2
                    
{-
Parse expressions.
An expression is:
expr ::=   expr `op` expr
      |    primExpr
-}
pExpr :: Parser Expr
pExpr = pTyped

pTyped :: Parser Expr
pTyped = do
                e <- pOp 
                mt <- option Nothing (Just <$ symbol "::" <*> parseType)
                case mt of
                    Nothing -> return e
                    Just t  -> return $ Typed e t

-- | The highest level of bindings or operator bindings. The parser created by the builder will parse as many
--   parts of an arithmatic, logical expression as possible. If there is no expression it will parse at least
--   one 'simpleExpr'.
pOp :: Parser Expr
pOp = buildExpressionParser operators pSimpleExpr
  where
    operators =
        [ [ binop "*"  AssocLeft, binop "/"  AssocLeft ]
        , [ binop "+"  AssocLeft, binop "-"  AssocLeft ]
--        , [ unop "-"]
        , [ binop "%"  AssocLeft, binop "contains"  AssocLeft]
        , [ binop "==" AssocNone, binop "!=" AssocNone, binop "<="  AssocNone
          , binop "<" AssocNone, binop ">="  AssocNone, binop ">" AssocNone ]
        , [ binop "&&" AssocRight ] -- Right for shortcircuiting
        , [ binop "||" AssocRight ] -- Right for shortcircuiting
        , [ elemOp "!" AssocLeft ]
        , [ binop ":" AssocRight ]
        ]
        where
          binop name assoc   = flip Infix assoc $ do
                                                    o <- parseOp name
                                                    return (\e1 e2 -> BinOp o e1 e2)
          elemOp name assoc = flip Infix assoc $ do
                                                    (Op _ i) <- parseOp name
                                                    return (\e1 e2 -> App (Var "index" i) [e1, e2])




parseOp :: String -> Parser Op
parseOp name = Op name <$ reservedOp name <*> (option 0 (fromInteger <$ symbol "^" <*> natural))

-- | A simpleExpr is an if, let, relationship, list comprehension or application.
{-
Parse primitive expressions, a primitive expression has the form:
primExpr ::= ifExpr | letExpr | iterExpr | appExpr | atom
-}
pSimpleExpr :: Parser Expr
pSimpleExpr = pIf <|> pLet <|> try pIter <|> try pApp <|> pAtom

-- | Parser for if then else contructs. The expression contained in the conditional and branches are
--   regular top level expression 'expr'.
{-
ifExpr ::= if expr then expr else expr
-}
pIf :: Parser Expr
pIf = If <$ reserved "if" <*> pExpr <* reserved "then" <*> pExpr <* reserved "else" <*> pExpr


-- | Parser for let bindings.
{-
letExpr ::= let i = expr in expr
-}
pLet :: Parser Expr
pLet = Let <$ reserved "let" <*> identifier <* symbol "=" <*> pExpr <* reserved "in" <*> pExpr

-- | Parser for function application. Parse an atomic expression followed by as much
--   atomic expressions as possible.If there is no application then parse at least
--   one atomic expression 'atom'.
{-
appExpr ::= var atom1 ... atomn
-}
pApp :: Parser Expr
pApp = App <$> pVariable <*> many1 pAtom

-- | Parse a variable.
pVariable :: Parser Expr
pVariable = Var <$> identifier <*> (option 0 $ fromInteger <$ symbol "^" <*> natural)


pIter :: Parser Expr
pIter = (\b i e g -> case g of
                        Nothing -> Iter i e b
                        Just g' -> IterG i e g' b) <$ symbol "[" <*> pExpr <* symbol "|" <*> identifier <* reservedOp "<-" <*> pExpr <*> (option Nothing $ Just <$ symbol "," <*> pExpr) <* symbol "]"


-- | Parser atomic values.
pAtom :: Parser Expr
pAtom = process <$> (list <|> constParser <|> parenExpr <|> pVariable) <*> many tLookup
 where
     tLookup :: Parser (Int, Int)
     tLookup = (\(Op _ l) i -> (l, fromInteger i)) <$> parseOp "@" <*> natural  
     process :: Expr -> [(Int, Int)] -> Expr
     process = foldl (\ex (l, i) -> Proj l ex i)
{-     
lookup ::=
    atom
    | atom @[^i] i 
  
-}   
-- | Parse a list.
list :: Parser Expr
list = do
        el <- squares $ commaSep pExpr
        return $ foldr cons Nil el

cons :: Expr -> Expr -> Expr
cons e1 e2 = BinOp (Op ":" 0) e1 e2

-- | Parse constant values. A constant is either a float, integer, string or boolean value.
constParser :: Parser Expr
constParser = Const <$> choice [
                                try intParser,
                                try negIntParser,
                                try boolParser
                                ]
             
-- | Parse a parenthesised expression. This is just an expression 'expr' surrounded by "( ... )"
parenExpr :: Parser Expr
parenExpr = do
              es <- parens (sepBy1 pExpr (symbol ","))
              case es of
                  [e] -> return e
                  _ -> return $ tuple es
                  
tuple :: [Expr] -> Expr
tuple es = let commas = replicate ((length es) - 1) ','
            in App (flip Var 0 $ "(" ++ commas ++ ")") es

{-
 Parsing primitive values
-}

-- | Parse an integer, currently only positive ints are allowed
intParser :: Parser Val
intParser = do
             v <- natural
             return (Int $ fromInteger v)
             
negIntParser :: Parser Val
negIntParser = do
                symbol "-"
                (Int v) <- intParser
                return (Int $ negate v)

-- | Parse a boolean value
boolParser :: Parser Val
boolParser = try trueParser
                <|> falseParser

trueParser :: Parser Val
trueParser = do
               reserved "True"
               return (Bool True)

falseParser :: Parser Val
falseParser = do
                reserved "False"
                return (Bool False)

parseType :: Parser T.Type 
parseType = parseFunctionType
    
parseFunctionType :: Parser T.Type
parseFunctionType = buildExpressionParser operators pSimpleType
  where
    operators =
        [ [ fun "->"  AssocRight]
        ]
        where
          fun name assoc   = flip Infix assoc $ do
                                                    parseOp name
                                                    return T.Fn

pSimpleType :: Parser T.Type
pSimpleType = try pVarType <|> try pIntType <|> try pBoolType <|> try pTupleType <|> pListType
    
 

pVarType :: Parser T.Type
pVarType = T.Var <$> identifier

pIntType :: Parser T.Type
pIntType = T.TyC "Int" [] <$ reserved "Int"

pBoolType :: Parser T.Type
pBoolType = T.TyC "Bool" [] <$ reserved "Bool"

pTupleType :: Parser T.Type
pTupleType = do
              es <- parens (sepBy1 parseType (symbol ","))
              case es of
                  [e] -> return e
                  _ -> return $ T.TyC "tuple" es
                  
pListType :: Parser T.Type
pListType = (\x -> T.TyC "List" [x]) <$ symbol "[" <*> parseType <* symbol "]"
             