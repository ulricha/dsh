{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Common.Lang where

import           Data.Aeson
import           Data.Aeson.TH
import qualified Data.List.NonEmpty           as N
import           Text.PrettyPrint.ANSI.Leijen
import           Text.Printf

import           Database.DSH.Common.Type
import           Database.DSH.Impossible

import           Database.DSH.Common.Nat

instance ToJSON a => ToJSON (N.NonEmpty a) where
    toJSON (n N.:| nl) = toJSON (n, nl)

instance FromJSON a => FromJSON (N.NonEmpty a) where
    parseJSON doc = parseJSON doc >>= \(n, nl) -> return $ n N.:| nl

-----------------------------------------------------------------------------
-- Common types for backend expressions

-- | Basic values in both FKL and NKL.
data Val where
    ListV   :: [Val] -> Val
    IntV    :: Int -> Val
    BoolV   :: Bool -> Val
    StringV :: String -> Val
    DoubleV :: Double -> Val
    TupleV  :: [Val] -> Val
    UnitV   :: Val
    deriving (Eq, Ord, Show)

newtype ColName = ColName String deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''ColName)

-- | Typed table columns
type Column = (ColName, Type)

-- | Table keys
newtype Key = Key [ColName] deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Key)

-- | Is the table guaranteed to be not empty?
data Emptiness = NonEmpty
               | PossiblyEmpty
               deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Emptiness)

-- | Catalog information hints that users may give to DSH
data TableHints = TableHints
    { keysHint     :: [Key]
    , nonEmptyHint :: Emptiness
    } deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''TableHints)

-- | Identifiers
type Ident = String


-----------------------------------------------------------------------------
-- Scalar operators

data UnCastOp = CastDouble
                deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''UnCastOp)

data UnBoolOp = Not
                deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''UnBoolOp)

data UnNumOp = Sin
             | Cos
             | Tan
             | ASin
             | ACos
             | ATan
             | Sqrt
             | Exp
             | Log
             deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''UnNumOp)

data UnTextOp = SubString Integer Integer
                deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''UnTextOp)

data ScalarUnOp = SUNumOp UnNumOp
                | SUBoolOp UnBoolOp
                | SUCastOp UnCastOp
                | SUTextOp UnTextOp
                | SUDateOp
                deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''ScalarUnOp)

data BinNumOp = Add
              | Sub
              | Div
              | Mul
              | Mod
              deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''BinNumOp)

data BinRelOp = Eq
              | Gt
              | GtE
              | Lt
              | LtE
              | NEq
              deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''BinRelOp)

data BinBoolOp = Conj
               | Disj
                deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''BinBoolOp)

data BinStringOp = Like
                   deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''BinStringOp)

-- FIXME this would be a good fit for PatternSynonyms
data ScalarBinOp = SBNumOp BinNumOp
                 | SBRelOp BinRelOp
                 | SBBoolOp BinBoolOp
                 | SBStringOp BinStringOp
                 deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''ScalarBinOp)


-----------------------------------------------------------------------------
-- Join operator arguments: limited expressions that can be used on joins

data JoinConjunct e = JoinConjunct e BinRelOp e
                    deriving (Show, Eq, Ord)

instance ToJSON e => ToJSON (JoinConjunct e) where
    toJSON (JoinConjunct e1 op e2) = toJSON (e1, op, e2)

instance FromJSON e => FromJSON (JoinConjunct e) where
    parseJSON d = parseJSON d >>= \(e1, op, e2) -> return $ JoinConjunct e1 op e2

newtype JoinPredicate e = JoinPred (N.NonEmpty (JoinConjunct e))
                        deriving (Show, Eq, Ord)

instance ToJSON e => ToJSON (JoinPredicate e) where
    toJSON (JoinPred conjs) = toJSON conjs

instance FromJSON e => FromJSON (JoinPredicate e) where
    parseJSON d = parseJSON d >>= \conjs -> return $ JoinPred conjs

singlePred :: JoinConjunct e -> JoinPredicate e
singlePred c = JoinPred $ c N.:| []

data JoinBinOp = JBNumOp BinNumOp
               | JBStringOp BinStringOp
               deriving (Show, Eq, Ord)

data JoinUnOp = JUNumOp UnNumOp
              | JUCastOp UnCastOp
              | JUTextOp UnTextOp
              deriving (Show, Eq, Ord)

data JoinExpr = JBinOp Type JoinBinOp JoinExpr JoinExpr
              | JUnOp Type JoinUnOp JoinExpr
              | JTupElem Type TupleIndex JoinExpr
              | JLit Type Val
              | JInput Type
              deriving (Show, Eq)

instance Typed JoinExpr where
    typeOf (JBinOp t _ _ _) = t
    typeOf (JUnOp t _ _)    = t
    typeOf (JTupElem t _ _) = t
    typeOf (JLit t _)       = t
    typeOf (JInput t)       = t

-----------------------------------------------------------------------------
-- Pretty-printing of stuff

parenthize :: JoinExpr -> Doc
parenthize e =
    case e of
        JBinOp _ _ _ _ -> parens $ pretty e
        JUnOp _ _ _    -> parens $ pretty e
        JTupElem _ _ _ -> pretty e
        JLit  _ _      -> pretty e
        JInput _       -> pretty e

instance Pretty Val where
    pretty (ListV xs)    = list $ map pretty xs
    pretty (IntV i)      = int i
    pretty (BoolV b)     = bool b
    pretty (StringV s)   = dquotes $ string s
    pretty (DoubleV d)   = double d
    pretty UnitV         = text "()"
    pretty (TupleV vs)   = tupled $ map pretty vs

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

instance Pretty BinBoolOp where
    pretty Conj = text "&&"
    pretty Disj = text "||"

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
    pretty (JUTextOp o) = pretty o

instance Pretty JoinBinOp where
    pretty (JBNumOp o)    = pretty o
    pretty (JBStringOp o) = pretty o

instance Pretty JoinExpr where
    pretty (JBinOp _ op e1 e2) = parenthize e1 <+> pretty op <+> parenthize e2
    pretty (JUnOp _ op e)      = pretty op <+> parenthize e
    pretty (JLit _ v)          = pretty v
    pretty (JInput _)          = text "I"
    pretty (JTupElem _ i e1)   =
        parenthize e1 <> dot <> int (tupleIndex i)

instance Pretty e => Pretty (JoinConjunct e) where
    pretty (JoinConjunct e1 op e2) = parens $ pretty e1 <+> pretty op <+> pretty e2

instance Pretty e => Pretty (JoinPredicate e) where
    pretty (JoinPred ps) = list $ map pretty $ N.toList ps


instance Pretty ScalarBinOp where
    pretty (SBNumOp o)    = pretty o
    pretty (SBRelOp o)    = pretty o
    pretty (SBBoolOp o)   = pretty o
    pretty (SBStringOp o) = pretty o

instance Pretty UnBoolOp where
    pretty Not = text "not"

instance Pretty ScalarUnOp where
    pretty (SUNumOp op)  = pretty op
    pretty (SUBoolOp op) = pretty op
    pretty (SUCastOp op) = pretty op
    pretty SUDateOp      = $unimplemented
    pretty (SUTextOp op) = pretty op

instance Pretty UnTextOp where
    pretty (SubString f t) = text $ printf "subString_%d,%d" f t
