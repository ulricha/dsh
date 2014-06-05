module Database.DSH.Common.Pretty 
  ( pp
  , Pretty, pretty
  ) where

import Text.PrettyPrint.ANSI.Leijen

pp :: Pretty a => a -> String
pp a = (displayS $ renderPretty 0.9 100 $ pretty a) ""
