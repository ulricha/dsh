{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE GADTs              #-}

module Database.DSH.Common.Lang where

import           Data.Data
import           Data.Typeable                ()
import           GHC.Generics

import           Data.List
import qualified Data.List.NonEmpty           as N
import           Text.PrettyPrint.ANSI.Leijen

import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type

-----------------------------------------------------------------------------
-- Common types for backend expressions

-- | Basic values in both FKL and NKL.
data Val where
    ListV   :: [Val] -> Val
    IntV    :: Int -> Val
    BoolV   :: Bool -> Val
    StringV :: String -> Val
    DoubleV :: Double -> Val
    PairV   :: Val -> Val -> Val
    UnitV   :: Val
    deriving (Eq, Ord, Generic, Data, Typeable)

instance Show Val where
  show (ListV vs)    = "[" ++ (intercalate ", " $ map show vs) ++ "]"
  show (IntV i)      = show i
  show (BoolV b)     = show b
  show (StringV s)   = "\"" ++ show s ++ "\""
  show (DoubleV d)   = show d
  show (PairV v1 v2) = "(" ++ show v1 ++ ", " ++ show v2 ++ ")"
  show UnitV         = "()"

newtype ColName = ColName String deriving (Eq, Ord, Show, Data, Typeable, Generic)

-- | Typed table columns
type Column = (ColName, Type)

-- | Table keys
newtype Key = Key [ColName] deriving (Eq, Ord, Show, Data, Typeable, Generic)

-- | Is the table guaranteed to be not empty?
data Emptiness = NonEmpty
               | PossiblyEmpty
               deriving (Eq, Ord, Show, Data, Typeable, Generic)

-- | Catalog information hints that users may give to DSH
data TableHints = TableHints
    { keysHint     :: [Key]
    , nonEmptyHint :: Emptiness
    } deriving (Eq, Ord, Show, Data, Typeable, Generic)

-- | Identifiers
type Ident = String

-----------------------------------------------------------------------------
-- Scalar operators

data UnCastOp = CastDouble
                deriving (Show, Eq, Ord, Generic, Data, Typeable)

data UnBoolOp = Not
                deriving (Show, Eq, Ord, Generic, Data, Typeable)

data UnNumOp = Sin
             | Cos
             | Tan
             | ASin
             | ACos
             | ATan
             | Sqrt
             | Exp
             | Log
             deriving (Show, Eq, Ord, Generic, Data, Typeable)

data ScalarUnOp = SUNumOp UnNumOp
                | SUBoolOp UnBoolOp
                | SUCastOp UnCastOp
                | SUDateOp
                deriving (Show, Eq, Ord, Generic, Data, Typeable)

data BinNumOp = Add
              | Sub
              | Div
              | Mul
              | Mod
              deriving (Show, Eq, Ord, Generic, Data, Typeable)

data BinRelOp = Eq
              | Gt
              | GtE
              | Lt
              | LtE
              | NEq
              deriving (Show, Eq, Ord, Generic, Data, Typeable)

data BinBoolOp = Conj
               | Disj
                deriving (Show, Eq, Ord, Generic, Data, Typeable)

data BinStringOp = Like -- | StringAppend | Contains
                   deriving (Show, Eq, Ord, Generic, Data, Typeable)

-- FIXME this would be a good fit for PatternSynonyms
data ScalarBinOp = SBNumOp BinNumOp
                 | SBRelOp BinRelOp
                 | SBBoolOp BinBoolOp
                 | SBStringOp BinStringOp
                 deriving (Show, Eq, Ord, Generic, Data, Typeable)


-----------------------------------------------------------------------------
-- Join operator arguments: limited expressions that can be used on joins

data JoinConjunct = JoinConjunct JoinExpr BinRelOp JoinExpr
                  deriving (Show, Eq, Ord, Generic, Data, Typeable)

newtype JoinPredicate = JoinPred (N.NonEmpty JoinConjunct)
                      deriving (Show, Eq, Ord, Generic, Data, Typeable)

singlePred :: JoinConjunct -> JoinPredicate
singlePred c = JoinPred $ c N.:| []

data JoinBinOp = JBNumOp BinNumOp
               | JBStringOp BinStringOp
               deriving (Show, Eq, Ord, Generic, Data, Typeable)

data JoinUnOp = JUNumOp UnNumOp
              | JUCastOp UnCastOp
              deriving (Show, Eq, Ord, Generic, Data, Typeable)

data JoinExpr = JBinOp Type JoinBinOp JoinExpr JoinExpr
              | JUnOp Type JoinUnOp JoinExpr
              | JFst Type JoinExpr
              | JSnd Type JoinExpr
              | JLit Type Val
              | JInput Type
              deriving (Show, Eq, Ord, Generic, Data, Typeable)

instance Typed JoinExpr where
    typeOf (JBinOp t _ _ _) = t
    typeOf (JUnOp t _ _)    = t
    typeOf (JFst t _)       = t
    typeOf (JSnd t _)       = t
    typeOf (JLit t _)       = t
    typeOf (JInput t)       = t

-----------------------------------------------------------------------------
-- Pretty-printing of stuff

parenthize :: JoinExpr -> Doc
parenthize e =
    case e of
        JBinOp _ _ _ _ -> parens $ pretty e
        JUnOp _ _ _    -> parens $ pretty e
        JFst _ _       -> parens $ pretty e
        JSnd _ _       -> parens $ pretty e
        JLit  _ _      -> pretty e
        JInput _       -> pretty e

instance Pretty Val where
    pretty (ListV xs)    = list $ map pretty xs
    pretty (IntV i)      = int i
    pretty (BoolV b)     = bool b
    pretty (StringV s)   = string s
    pretty (DoubleV d)   = double d
    pretty (PairV v1 v2) = tupled $ [ pretty v1, pretty v2 ]
    pretty UnitV         = text "()"

instance Pretty BinRelOp where
    pretty Eq  = text "=="
    pretty Gt  = text ">"
    pretty Lt  = text "<"
    pretty GtE = text ">="
    pretty LtE = text "<="
    pretty NEq = text "/="

instance Pretty BinStringOp where
    pretty Like = text "LIKE"

instance Pretty BinNumOp where
    pretty Add = text "+"
    pretty Sub = text "-"
    pretty Div = text "/"
    pretty Mul = text "*"
    pretty Mod = text "%"

instance Pretty UnNumOp where
    pretty Sin  = text "sin"
    pretty Cos  = text "cos"
    pretty Tan  = text "tan"
    pretty Sqrt = text "sqrt"
    pretty Exp  = text "exp"
    pretty Log  = text "log"
    pretty ASin = text "asin"
    pretty ACos = text "acos"
    pretty ATan = text "atan"

instance Pretty UnCastOp where
    pretty CastDouble = text "double"

instance Pretty JoinUnOp where
    pretty (JUNumOp o)  = pretty o
    pretty (JUCastOp o) = pretty o

instance Pretty JoinBinOp where
    pretty (JBNumOp o)    = pretty o
    pretty (JBStringOp o) = pretty o

instance Pretty JoinExpr where
    pretty (JBinOp _ op e1 e2) = parenthize e1 <+> pretty op <+> parenthize e2
    pretty (JUnOp _ op e)      = pretty op <+> parenthize e
    pretty (JFst _ e)          = text "fst" <+> parenthize e
    pretty (JSnd _ e)          = text "snd" <+> parenthize e
    pretty (JLit _ v)          = pretty v
    pretty (JInput _)          = text "INP"

instance Pretty JoinConjunct where
    pretty (JoinConjunct e1 op e2) = parens $ pretty e1 <+> pretty op <+> pretty e2

instance Pretty JoinPredicate where
    pretty (JoinPred ps) = brackets $ hsep $ punctuate (text "&&") $ map pretty $ N.toList ps
