module Optimizer.VL.Properties.Types where

import Text.PrettyPrint
  

-- import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data
import Database.Algebra.VL.Render.Dot

data VectorProp a = VProp a
                  | VPropPair a a
                  | VPropTriple a a a
                    
instance Show a => Show (VectorProp a) where
  show (VProp a) = show a
  show (VPropPair a1 a2) = show (a1, a2)
  show (VPropTriple a1 a2 a3) = show (a1, a2, a3)
                    
data VectorType = ValueVector Int
                | AtomicVector Int
                | DescrVector
                | RenameVector
                | PropVector
                deriving Show
                       
{-
-- newtype PredExpr = VecOp AlgNode AlgNode
                       
data Predicate = Pred VecOp DBCol DBCol
                 deriving (Show, Eq)
                       
{- Index space transformation -}
data ISTrans = PredT Predicate ISTrans
             | SelectT ISTrans
             | NumberT ISTrans
             | ConstT ISTrans
             | PosSeed AlgNode
             | DescrSeed AlgNode
             deriving Show
                      
newtype PosIS = P ISTrans deriving Show
newtype DescrIS = D ISTrans deriving Show
newtype SourceIS = S ISTrans deriving Show
newtype TargetIS = T ISTrans deriving Show
                      
data IS = DBVSpace DescrIS PosIS
        | DBPSpace
        | DescrVectorSpace DescrIS PosIS
        | RenameVectorTransform SourceIS TargetIS
        | PropVectorTransform
          deriving Show
-}
                       
data Const = Const VLVal
           | NoConst
            deriving Show 
             
data ConstDescr = ConstDescr Nat
                | NonConstDescr

data ConstPayload = ConstPL VLVal
                  | NonConstPL
                  deriving Show 
             
data ConstVec = DBVConst ConstDescr [ConstPayload]
              | DescrVecConst ConstDescr
              | RenameVecConst SourceConstDescr TargetConstDescr
              | DBPConst [ConstPayload]
              | PropVecConst SourceConstDescr TargetConstDescr
              deriving Show 
                       
newtype SourceConstDescr = SC ConstDescr deriving Show
newtype TargetConstDescr = TC ConstDescr deriving Show
                       
data BottomUpProps = BUProps { emptyProp :: VectorProp Bool 
                             , constProp :: VectorProp ConstVec
                             , card1Prop :: VectorProp Bool
                             , vectorTypeProp :: VectorProp VectorType } deriving (Show)
                                                                                
data TopDownProps = TDProps { toDescrProp :: VectorProp (Maybe Bool) }
                    
data Properties = P { bu :: BottomUpProps
                    , td :: TopDownProps }
                  
class Renderable a where
  renderProp :: a -> Doc
  
c :: Doc -> Doc -> Doc
c d1 d2 = d1 <> comma <+> d2
  
instance Renderable a => Renderable (VectorProp a) where
  renderProp (VProp p)              = renderProp p
  renderProp (VPropPair p1 p2)      = parens $ (renderProp p1) `c` (renderProp p2)
  renderProp (VPropTriple p1 p2 p3) = parens $ (renderProp p1) `c` (renderProp p2) `c` (renderProp p3)
  
instance Renderable Bool where
  renderProp = text . show

bracketList :: (a -> Doc) -> [a] -> Doc
bracketList f = brackets . hsep . punctuate comma . map f
                
instance Show ConstDescr where
  show (ConstDescr v) = render $ renderTblVal (VLNat v)
  show NonConstDescr  = "NC"
  
instance Renderable ConstVec where
  renderProp (DBVConst d ps) = (text $ show d) <+> payload
    where payload = bracketList id $ map renderPL $ foldr isConst [] $ zip [1..] ps
          isConst (_, NonConstPL) vals   = vals
          isConst (i, (ConstPL v)) vals  = (i, v) : vals
          
          renderPL (i, v)  = int i <> colon <> renderTblVal v

          bracketList :: (a -> Doc) -> [a] -> Doc
          bracketList f = brackets . hsep . punctuate comma . map f

  renderProp (DBPConst ps) = payload
    where payload = bracketList id $ map renderPL $ foldr isConst [] $ zip [1..] ps
          isConst (_, NonConstPL) vals   = vals
          isConst (i, (ConstPL v)) vals  = (i, v) : vals
          
          renderPL (i, v)  = int i <> colon <> renderTblVal v

          bracketList :: (a -> Doc) -> [a] -> Doc
          bracketList f = brackets . hsep . punctuate comma . map f

  renderProp (RenameVecConst (SC ds) (TC ts)) = (text $ show ds) <> text " -> " <> (text $ show ts)
  renderProp (PropVecConst (SC ds) (TC ts)) = (text $ show ds) <> text " -> " <> (text $ show ts)
  renderProp c = text $ show c

instance Renderable VectorType where
  renderProp = text . show
  
instance Renderable BottomUpProps where
  renderProp p = text "empty:" <+> (renderProp $ emptyProp p)
                 $$ text "const:" <+> (renderProp $ constProp p)
                 $$ text "schema:" <+> (renderProp $ vectorTypeProp p)
                 
instance Renderable TopDownProps where
  renderProp p = text "toDescr:" <+> (text $ show $ toDescrProp p)
  
-- | Rendering function for the bottom-up properties container.
renderBottomUpProps :: BottomUpProps -> [String]
renderBottomUpProps ps = [render $ renderProp ps]
                         
renderTopDownProps :: TopDownProps -> [String]
renderTopDownProps ps = [render $ renderProp ps]
                         
renderProperties  :: Properties -> [String]
renderProperties ps = (renderBottomUpProps $ bu ps) ++ (renderTopDownProps $ td ps)
