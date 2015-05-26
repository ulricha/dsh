module Database.DSH.Common.Pretty
  ( pp
  , Pretty, pretty
  , combinator, join, comp, super, sub, forget, kw, dist, restrict
  , prettyJoin, prettyComp, prettyApp2, prettyUnOp
  , prettyInfixBinOp, prettyPrefixBinOp
  ) where

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as P

pp :: Pretty a => a -> String
pp a = (displayS $ renderPretty 0.9 140 $ pretty a) ""

--------------------------------------------------------------------------------
-- Highlighting of various syntactical elements

combinator :: Doc -> Doc
combinator = id

kw :: Doc -> Doc
kw = bold

join :: Doc -> Doc
join = green

comp :: Doc -> Doc
comp = red

super :: Doc -> Doc
super = red

sub :: Doc -> Doc
sub = red

forget :: Doc -> Doc
forget = blue

restrict :: Doc -> Doc
restrict = yellow

dist :: Doc -> Doc
dist = cyan

--------------------------------------------------------------------------------
-- Pretty-printing of various syntactical elements

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
    left   = red lbracket
    right  = red rbracket

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
