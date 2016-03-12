{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.Common.Lang where

import           Data.Aeson
import           Data.Aeson.TH
import qualified Data.List.NonEmpty           as N
import           Data.Scientific
import qualified Data.Text                    as T
import qualified Data.Time.Calendar           as C
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import           Text.Printf

import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type

instance ToJSON a => ToJSON (N.NonEmpty a) where
    toJSON (n N.:| nl) = toJSON (n, nl)

instance FromJSON a => FromJSON (N.NonEmpty a) where
    parseJSON doc = parseJSON doc >>= \(n, nl) -> return $ n N.:| nl

-----------------------------------------------------------------------------
-- Common types for backend expressions

-- | Basic values in both FKL and NKL.
data Val = ListV    [Val]
         | TupleV   [Val]
         | ScalarV  ScalarVal
         deriving (Eq, Ord, Show)

instance FromJSON Date where
    parseJSON o = Date . (\(y, m, d) -> C.fromGregorian y m d) <$> parseJSON o

instance ToJSON Date where
    toJSON = toJSON . C.toGregorian . unDate

newtype Date = Date { unDate :: C.Day } deriving (Eq, Ord, Show)

data ScalarVal = IntV      Int
               | BoolV     Bool
               | StringV   T.Text
               | DoubleV   Double
               | DecimalV  Scientific
               | DateV     Date
               | UnitV
               deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''ScalarVal)

newtype ColName = ColName String deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''ColName)

-- | Typed table columns
type ColumnInfo = (ColName, ScalarType)

-- | Table keys
newtype Key = Key (N.NonEmpty ColName) deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Key)

-- | Is the table guaranteed to be not empty?
data Emptiness = NonEmpty
               | PossiblyEmpty
               deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Emptiness)

-- | Information about base tables
data BaseTableSchema = BaseTableSchema
    { tableCols     :: N.NonEmpty ColumnInfo
    , tableKeys     :: N.NonEmpty Key
    , tableNonEmpty :: Emptiness
    } deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''BaseTableSchema)

-- | Identifiers
type Ident = String

-----------------------------------------------------------------------------

-- | A wrapper around 'NonEmpty' lists to avoid an orphan instance for 'Pretty'.
newtype NE a = NE { getNE :: N.NonEmpty a } deriving (Eq, Ord, Show)

instance Pretty a => Pretty (NE a) where
    pretty (NE xs) = pretty $ N.toList xs

instance Functor NE where
    fmap f (NE xs) = NE (fmap f xs)

$(deriveJSON defaultOptions ''NE)

-----------------------------------------------------------------------------
-- Scalar operators

data UnCastOp = CastDouble
              | CastDecimal
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

data UnDateOp = DateDay
              | DateMonth
              | DateYear
              deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''UnDateOp)

data ScalarUnOp = SUNumOp UnNumOp
                | SUBoolOp UnBoolOp
                | SUCastOp UnCastOp
                | SUTextOp UnTextOp
                | SUDateOp UnDateOp
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

data BinDateOp = AddDays
               | SubDays
               | DiffDays
               deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''BinDateOp)

-- FIXME this would be a good fit for PatternSynonyms
data ScalarBinOp = SBNumOp BinNumOp
                 | SBRelOp BinRelOp
                 | SBBoolOp BinBoolOp
                 | SBStringOp BinStringOp
                 | SBDateOp BinDateOp
                 deriving (Show, Eq, Ord)

$(deriveJSON defaultOptions ''ScalarBinOp)

-----------------------------------------------------------------------------
-- Aggregate

-- | AggrFun functions
data AggrFun = Length | Avg | Minimum | Maximum | And | Or | Sum
    deriving (Eq, Show)

data AggrApp = AggrApp
    { aaFun :: AggrFun
    , aaArg :: ScalarExpr
    } deriving (Eq, Show)

aggType :: AggrApp -> Type
aggType (AggrApp af e) = aggFunType af $ typeOf e

aggFunType :: AggrFun -> Type -> Type
aggFunType Length _   = PIntT
aggFunType Sum ty     = ty
aggFunType Maximum ty = ty
aggFunType Minimum ty = ty
aggFunType Avg ty     = ty
aggFunType And _      = PBoolT
aggFunType Or _       = PBoolT

instance Pretty AggrFun where
  pretty Length          = combinator $ text "length"
  pretty Sum             = combinator $ text "sum"
  pretty Avg             = combinator $ text "avg"
  pretty Minimum         = combinator $ text "minimum"
  pretty Maximum         = combinator $ text "maximum"
  pretty And             = combinator $ text "and"
  pretty Or              = combinator $ text "or"

instance Pretty AggrApp where
    pretty aa = pretty (aaFun aa) <> parens (pretty $ aaArg aa)

-----------------------------------------------------------------------------
-- Join operator arguments: limited expressions that can be used on joins

data JoinConjunct e = JoinConjunct
    { jcLeft  :: e
    , jcOp    :: BinRelOp
    , jcRight :: e
    } deriving (Show, Eq, Ord)

instance ToJSON e => ToJSON (JoinConjunct e) where
    toJSON (JoinConjunct e1 op e2) = toJSON (e1, op, e2)

instance FromJSON e => FromJSON (JoinConjunct e) where
    parseJSON d = parseJSON d >>= \(e1, op, e2) -> return $ JoinConjunct e1 op e2

newtype JoinPredicate e = JoinPred { jpConjuncts :: N.NonEmpty (JoinConjunct e) }
    deriving (Show, Eq, Ord)

instance ToJSON e => ToJSON (JoinPredicate e) where
    toJSON (JoinPred conjs) = toJSON conjs

instance FromJSON e => FromJSON (JoinPredicate e) where
    parseJSON d = parseJSON d >>= \conjs -> return $ JoinPred conjs

singlePred :: JoinConjunct e -> JoinPredicate e
singlePred c = JoinPred $ c N.:| []

data ScalarExpr = JBinOp Type ScalarBinOp ScalarExpr ScalarExpr
                | JUnOp Type ScalarUnOp ScalarExpr
                | JTupElem Type TupleIndex ScalarExpr
                | JLit Type Val
                | JInput Type
              deriving (Show, Eq)

instance Typed ScalarExpr where
    typeOf (JBinOp t _ _ _) = t
    typeOf (JUnOp t _ _)    = t
    typeOf (JTupElem t _ _) = t
    typeOf (JLit t _)       = t
    typeOf (JInput t)       = t

-----------------------------------------------------------------------------
-- Pretty-printing of stuff

parenthize :: ScalarExpr -> Doc
parenthize e =
    case e of
        JBinOp{}   -> parens $ pretty e
        JUnOp{}    -> parens $ pretty e
        JTupElem{} -> pretty e
        JLit{}     -> pretty e
        JInput{}   -> pretty e

instance Pretty Val where
    pretty (ListV xs)    = list $ map pretty xs
    pretty (TupleV vs)   = tupled $ map pretty vs
    pretty (ScalarV v)   = pretty v

instance Pretty ScalarVal where
    pretty (IntV i)        = int i
    pretty (BoolV b)       = bool b
    pretty (StringV t)     = dquotes $ string $ T.unpack t
    pretty (DoubleV d)     = double d
    pretty (DecimalV d)    = text $ show d
    pretty UnitV           = text "()"
    pretty (DateV d)       = text $ C.showGregorian $ unDate d

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


instance Pretty BinDateOp where
    pretty AddDays  = text "addDays"
    pretty SubDays  = text "subDays"
    pretty DiffDays = text "diffDays"

isBinInfixOp :: ScalarBinOp -> Bool
isBinInfixOp op =
    case op of
        SBNumOp{}    -> True
        SBRelOp{}    -> True
        SBBoolOp{}   -> True
        SBStringOp{} -> False
        SBDateOp{}   -> False

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
    pretty CastDouble  = text "double"
    pretty CastDecimal = text "decimal"

instance Pretty UnDateOp where
    pretty DateDay   = text "dateDay"
    pretty DateMonth = text "dateMonth"
    pretty DateYear  = text "dateYear"

instance Pretty ScalarExpr where
    pretty (JBinOp _ op e1 e2) = parenthize e1 <+> pretty op <+> parenthize e2
    pretty (JUnOp _ op e)      = pretty op <+> parenthize e
    pretty (JLit _ v)          = pretty v
    pretty (JInput _)          = text "I"
    pretty (JTupElem _ i e1)   =
        parenthize e1 <> dot <> int (tupleIndex i)

instance Pretty e => Pretty (JoinConjunct e) where
    pretty (JoinConjunct e1 op e2) = pretty e1 <+> pretty op <+> pretty e2

instance Pretty e => Pretty (JoinPredicate e) where
    pretty (JoinPred ps) = hcat $ punctuate (text " && ") $ map pretty $ N.toList ps

instance Pretty ScalarBinOp where
    pretty (SBNumOp o)    = pretty o
    pretty (SBRelOp o)    = pretty o
    pretty (SBBoolOp o)   = pretty o
    pretty (SBStringOp o) = pretty o
    pretty (SBDateOp o)   = pretty o

instance Pretty UnBoolOp where
    pretty Not = text "not"

instance Pretty ScalarUnOp where
    pretty (SUNumOp op)  = pretty op
    pretty (SUBoolOp op) = pretty op
    pretty (SUCastOp op) = pretty op
    pretty (SUDateOp op) = pretty op
    pretty (SUTextOp op) = pretty op

instance Pretty UnTextOp where
    pretty (SubString f t) = text $ printf "subString_%d,%d" f t
