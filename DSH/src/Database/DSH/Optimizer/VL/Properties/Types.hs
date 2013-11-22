module Database.DSH.Optimizer.VL.Properties.Types where

import           Text.PrettyPrint

import           Database.Algebra.Dag.Common
import           Database.Algebra.VL.Data
import           Database.Algebra.VL.Render.Dot

data VectorProp a = VProp a
                  | VPropPair a a
                  | VPropTriple a a a

instance Show a => Show (VectorProp a) where
  show (VProp a) = show a
  show (VPropPair a1 a2) = show (a1, a2)
  show (VPropTriple a1 a2 a3) = show (a1, a2, a3)

data VectorType = ValueVector Int
                | AtomicVector Int
                | RenameVector
                | PropVector
                deriving Show

data Const = Const VLVal
           | NoConst
            deriving Show

data ConstDescr = ConstDescr Nat
                | NonConstDescr

data ConstPayload = ConstPL VLVal
                  | NonConstPL
                  deriving Show

data ConstVec = DBVConst ConstDescr [ConstPayload]
              | RenameVecConst SourceConstDescr TargetConstDescr
              | DBPConst [ConstPayload]
              | PropVecConst SourceConstDescr TargetConstDescr
              deriving Show

newtype SourceConstDescr = SC ConstDescr deriving Show
newtype TargetConstDescr = TC ConstDescr deriving Show

data BottomUpProps = BUProps { emptyProp            :: VectorProp Bool
                             , constProp            :: VectorProp ConstVec
                             , card1Prop            :: VectorProp Bool
                             , vectorTypeProp       :: VectorProp VectorType
                             } deriving (Show)


type ReqCols = Maybe [DBCol]

data TopDownProps = TDProps { reqColumnsProp :: VectorProp ReqCols }

data Properties = Properties { bu :: BottomUpProps
                             , td :: TopDownProps }

class Renderable a where
  renderProp :: a -> Doc

insertComma :: Doc -> Doc -> Doc
insertComma d1 d2 = d1 <> comma <+> d2

instance Renderable a => Renderable (VectorProp a) where
  renderProp (VProp p)              = renderProp p
  renderProp (VPropPair p1 p2)      = parens $ (renderProp p1) `insertComma` (renderProp p2)
  renderProp (VPropTriple p1 p2 p3) = parens $ (renderProp p1) `insertComma` (renderProp p2) `insertComma` (renderProp p3)

instance Renderable a => Renderable (Maybe a) where
  renderProp (Just x) = renderProp x
  renderProp Nothing  = text "na"

instance Renderable Bool where
  renderProp = text . show

bracketList :: (a -> Doc) -> [a] -> Doc
bracketList f = brackets . hsep . punctuate comma . map f

instance Renderable Int where
  renderProp = text . show

instance Renderable a => Renderable [a] where
  renderProp = bracketList renderProp

instance Show ConstDescr where
  show (ConstDescr v) = render $ renderTblVal (VLNat v)
  show NonConstDescr  = "NC"

instance Renderable ConstVec where
  renderProp (DBVConst d ps) = (text $ show d) <+> payload
    where payload = bracketList id $ map renderPL $ foldr isConst [] $ zip [1..] ps
          isConst (_, NonConstPL) vals   = vals
          isConst (i, (ConstPL v)) vals  = (i, v) : vals

          renderPL (i, v)  = int i <> colon <> renderTblVal v

  renderProp (DBPConst ps) = payload
    where payload = bracketList id $ map renderPL $ foldr isConst [] $ zip [1..] ps
          isConst (_, NonConstPL) vals   = vals
          isConst (i, (ConstPL v)) vals  = (i, v) : vals

          renderPL (i, v)  = int i <> colon <> renderTblVal v

  renderProp (RenameVecConst (SC ds) (TC ts)) = (text $ show ds) <> text " -> " <> (text $ show ts)
  renderProp (PropVecConst (SC ds) (TC ts)) = (text $ show ds) <> text " -> " <> (text $ show ts)

instance Renderable VectorType where
  renderProp = text . show

instance Renderable BottomUpProps where
  renderProp p = text "empty:" <+> (renderProp $ emptyProp p)
                 $$ text "const:" <+> (renderProp $ constProp p)
                 $$ text "schema:" <+> (renderProp $ vectorTypeProp p)

instance Renderable TopDownProps where
  renderProp p = text "reqCols:" <+> (text $ show $ reqColumnsProp p)

-- | Rendering function for the bottom-up properties container.
renderBottomUpProps :: BottomUpProps -> [String]
renderBottomUpProps ps = [render $ renderProp ps]

renderTopDownProps :: TopDownProps -> [String]
renderTopDownProps ps = [render $ renderProp ps]

renderProperties  :: Properties -> [String]
renderProperties ps = (renderBottomUpProps $ bu ps) ++ (renderTopDownProps $ td ps)
