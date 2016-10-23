module Database.DSH.SL.Opt.Properties.Types where

import           Prelude hiding ((<$>))
import           Text.PrettyPrint.ANSI.Leijen

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.VectorLang

data VectorProp a = VProp a
                  | VPropPair a a
                  | VPropTriple a a a

instance Show a => Show (VectorProp a) where
  show (VProp a) = show a
  show (VPropPair a1 a2) = show (a1, a2)
  show (VPropTriple a1 a2 a3) = show (a1, a2, a3)

data VectorType = VTDataVec PType
                | VTNA
                deriving Show

data ConstPayload = CPTuple ![ConstPayload]
                  | CPVal   !ScalarVal
                  | CPNoVal
           deriving (Show)

data ConstVec = ConstVec ConstPayload
              | CNA
              deriving (Show)

data SegP = UnitSegP | SegdP | SegNAP deriving (Show)

data BottomUpProps = BUProps
    { emptyProp      :: VectorProp Bool
    -- , constProp      :: VectorProp ConstVec
    , card1Prop      :: VectorProp Bool
    -- , vectorTypeProp :: VectorProp VectorType
    , segProp        :: VectorProp SegP
    } deriving (Show)

data TopDownProps = TDProps deriving (Show)

data Properties = Properties { bu :: BottomUpProps
                             , td :: TopDownProps
                             }

insertComma :: Doc -> Doc -> Doc
insertComma d1 d2 = d1 <> comma <+> d2

instance Pretty a => Pretty (VectorProp a) where
  pretty (VProp p)              = pretty p
  pretty (VPropPair p1 p2)      = parens $ (pretty p1) `insertComma` (pretty p2)
  pretty (VPropTriple p1 p2 p3) = parens $ (pretty p1) `insertComma` (pretty p2) `insertComma` (pretty p3)

bracketList :: (a -> Doc) -> [a] -> Doc
bracketList f = brackets . hsep . punctuate comma . map f

instance Pretty ConstVec where
  pretty (ConstVec v) = pretty v
  pretty CNA          = text "NA"

instance Pretty ConstPayload where
    pretty (CPTuple vs) = tupled $ map pretty vs
    pretty (CPVal v)    = pretty v
    pretty CPNoVal      = text "nc"

instance Pretty VectorType where
  pretty = text . show

instance Pretty BottomUpProps where
  pretty p = text "empty:" <+> (pretty $ emptyProp p)
                 -- <$> text "const:" <+> (pretty $ constProp p)
                 -- <$> text "schema:" <+> (pretty $ vectorTypeProp p)

instance Pretty TopDownProps where
  pretty _ = empty

-- | Rendering function for the bottom-up properties container.
renderBottomUpProps :: BottomUpProps -> [String]
renderBottomUpProps ps = [pp $ pretty ps]

renderTopDownProps :: TopDownProps -> [String]
renderTopDownProps ps = [pp $ pretty ps]

prettyerties  :: Properties -> [String]
prettyerties ps = (renderBottomUpProps $ bu ps) ++ (renderTopDownProps $ td ps)
