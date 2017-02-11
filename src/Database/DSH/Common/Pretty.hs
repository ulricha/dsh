module Database.DSH.Common.Pretty
  ( pp
  , Pretty, pretty
  , combinator, join, comp, super, sub, forget, kw, dist, restrict
  , prettyJoin, prettyComp, prettyApp2, prettyUnOp
  , prettyInfixBinOp, prettyPrefixBinOp, prettyLet, prettyIf
  , prettyTuple, prettyFun
  , prettyTupTy, prettyTupConst
  ) where

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as P

pp :: Pretty a => a -> String
pp a = (displayS $ renderPretty 0.9 140 $ pretty a) ""

--------------------------------------------------------------------------------
-- Highlighting of various syntactical elements

combinator :: Doc -> Doc
combinator = dullyellow

kw :: Doc -> Doc
kw = bold

join :: Doc -> Doc
join = yellow

comp :: Doc -> Doc
comp = red

tuple :: Doc -> Doc
tuple = green

super :: Doc -> Doc
super = red

sub :: Doc -> Doc
sub = red

forget :: Doc -> Doc
forget = blue

restrict :: Doc -> Doc
restrict = magenta

dist :: Doc -> Doc
dist = cyan

--------------------------------------------------------------------------------
-- Pretty-printing of various syntactical elements

prettyIf :: Doc -> Doc -> Doc -> Doc
prettyIf c t e =
    group $ align $ kw (text "if") <+> c
                    P.<$> kw (text "then") <+> t
                    P.<$> kw (text "else") <+> e

prettyLet :: Doc -> Doc -> Doc -> Doc
prettyLet x e1 e2 =
    group $ align $ (kw (text "let") <+> x <+> kw (char '=') <+> e1)
                    P.<$>
                    kw (text "in") <+> e2


prettyTuple :: [Doc] -> Doc
prettyTuple es =
    case es of
        [] -> left <+> right
        [e] -> left <+> e <+> right
        (e1:e2:es') ->
            align $ cat $ [left <+> e1]
                          ++
                          (map (tuple comma <+>) $ init (e2 : es'))
                          ++
                          [tuple comma <+> last (e2 : es') <> space]
                          ++
                          [right]

  where
    left  = tuple $ char '〈'
    right = tuple $ char '〉'

prettyComp :: Doc -> [Doc] -> Doc
prettyComp headExpr quals
    = case quals of
        []  -> left <+> headExpr <+> right
        (q:qs) ->
            -- We have to insert spaces after the head expression (for
            -- '|') and after the last qualifier (for '|') for the
            -- case of the comprehension being rendered on one line.
            let qsDocs = comp (char '|') <+> q : map (comp comma <+>) qs
            in align $ cat $ (left <+> headExpr <> space)
                             :
                             (init qsDocs)
                             ++
                             [last qsDocs <> space]
                             ++
                             [right]
  where
    left   = comp lbracket
    right  = comp rbracket

prettyJoin :: Doc -> Doc -> Doc -> Doc
prettyJoin op xs ys =
    group $ hang 4 $ op P.<$> (vsep [xs, ys])

prettyApp2 :: Doc -> Doc -> Doc -> Doc
prettyApp2 op xs ys =
    group $ op <+> (align $ xs P.<$> ys)

prettyUnOp :: Doc -> Doc -> Doc
prettyUnOp op x =
    op <+> x

prettyInfixBinOp :: Doc -> Doc -> Doc -> Doc
prettyInfixBinOp op x y =
    group $ (align $ x P.<$> op P.<$> y)

prettyPrefixBinOp :: Doc -> Doc -> Doc -> Doc
prettyPrefixBinOp op x y =
    group $ op <+> (align $ x P.<$> y)

prettyFun :: Doc -> [Doc] -> Doc
prettyFun name args = name <> parens (hsep $ punctuate comma args)

prettyTupTy :: [Doc] -> Doc
prettyTupTy = encloseSep (char '〈') (char '〉') comma

prettyTupConst :: [Doc] -> Doc
prettyTupConst = prettyTupTy
