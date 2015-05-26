module Database.DSH.Common.Pretty
  ( pp
  , Pretty, pretty
  , combinator, join, prettyComp, comp, super, sub, forget, kw, dist, restrict
  ) where

import Text.PrettyPrint.ANSI.Leijen

pp :: Pretty a => a -> String
pp a = (displayS $ renderPretty 0.9 120 $ pretty a) ""

combinator :: Doc -> Doc
combinator = id

kw :: Doc -> Doc
kw = bold

join :: Doc -> Doc
join = green

prettyComp :: Doc -> [Doc] -> Doc
prettyComp headExpr quals
    = case quals of
        []  -> left <+> headExpr <+> right
        (q:qs) -> align $ cat $ [ left <+> headExpr
                                , comp (char '|') <+> q
                                ]
                                ++
                                (map (comp comma <+>) qs)
                                ++
                                [right]

  where
    left = red lbracket
    right = red rbracket

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
