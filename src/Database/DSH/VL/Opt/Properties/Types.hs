module Database.DSH.VL.Opt.Properties.Types where

import           Text.PrettyPrint.ANSI.Leijen

import           Database.DSH.VL.Lang
import           Database.DSH.Common.Pretty
import           Database.DSH.VL.Render.Dot

data VectorProp a = VProp a
                  | VPropPair a a
                  | VPropTriple a a a

instance Show a => Show (VectorProp a) where
  show (VProp a) = show a
  show (VPropPair a1 a2) = show (a1, a2)
  show (VPropTriple a1 a2 a3) = show (a1, a2, a3)

data VectorType = ValueVector Int
                | RenameVector
                | PropVector
                deriving Show

data Const = Const VLVal
           | NoConst
            deriving Show

data ConstDescr = ConstDescr Int
                | NonConstDescr

data ConstPayload = ConstPL VLVal
                  | NonConstPL
                  deriving Show

data ConstVec = DBVConst ConstDescr [ConstPayload]
              | RenameVecConst SourceConstDescr TargetConstDescr
              | PropVecConst SourceConstDescr TargetConstDescr
              deriving Show

newtype SourceConstDescr = SC ConstDescr deriving Show
newtype TargetConstDescr = TC ConstDescr deriving Show

data BottomUpProps = BUProps { emptyProp            :: VectorProp Bool
                             -- Documents wether a vector is
                             -- statically known to be not empty. For
                             -- a flat vector (i.e. a vector with only
                             -- one segment) t his property is true if
                             -- we can statically decide that the
                             -- vector is not empty. For an inner
                             -- vector, i.e. a vector with multiple
                             -- segments, it is true if *every*
                             -- segment is non-empty.
                             , nonEmptyProp         :: VectorProp Bool
                             , constProp            :: VectorProp ConstVec
                             , card1Prop            :: VectorProp Bool
                             , vectorTypeProp       :: VectorProp VectorType
                             } deriving (Show)


type ReqCols = Maybe [DBCol]

data TopDownProps = TDProps { reqColumnsProp :: VectorProp ReqCols } deriving (Show)

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

instance Show ConstDescr where
  show (ConstDescr v) = pp $ int v
  show NonConstDescr  = "NC"

instance Pretty ConstVec where
  pretty (DBVConst d ps) = (text $ show d) <+> payload
    where payload = bracketList id $ map renderPL $ foldr isConst [] $ zip [1..] ps
          isConst (_, NonConstPL) vals   = vals
          isConst (i, (ConstPL v)) vals  = (i, v) : vals

          renderPL (i, v)  = int i <> colon <> renderTblVal v

  pretty (RenameVecConst (SC ds) (TC ts)) = (text $ show ds) <> text " -> " <> (text $ show ts)
  pretty (PropVecConst (SC ds) (TC ts)) = (text $ show ds) <> text " -> " <> (text $ show ts)

instance Pretty VectorType where
  pretty = text . show

instance Pretty BottomUpProps where
  pretty p = text "empty:" <+> (pretty $ emptyProp p)
                 <$> text "const:" <+> (pretty $ constProp p)
                 <$> text "schema:" <+> (pretty $ vectorTypeProp p)

instance Pretty TopDownProps where
  pretty p = text "reqCols:" <+> (text $ show $ reqColumnsProp p)

-- | Rendering function for the bottom-up properties container.
renderBottomUpProps :: BottomUpProps -> [String]
renderBottomUpProps ps = [pp $ pretty ps]

renderTopDownProps :: TopDownProps -> [String]
renderTopDownProps ps = [pp $ pretty ps]

prettyerties  :: Properties -> [String]
prettyerties ps = (renderBottomUpProps $ bu ps) ++ (renderTopDownProps $ td ps)
