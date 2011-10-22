module Database.DSH.XHTML (xhtmlExport, xhtmlExportHandle, xhtmlExportStdout) where

import Database.DSH.Data hiding (table)

import Text.XHtml.Strict

import qualified Data.Text as Text

import qualified System.IO as IO
import System.IO (Handle)

xhtmlExport :: (QA a) => FilePath -> [a] -> IO ()
xhtmlExport file as = IO.withFile file IO.WriteMode (\handle -> xhtmlExportHandle handle as)

xhtmlExportStdout :: (QA a) => [a] -> IO ()
xhtmlExportStdout = xhtmlExportHandle IO.stdout

xhtmlExportHandle :: (QA a) => Handle -> [a] -> IO ()
xhtmlExportHandle handle as = IO.hPutStr handle (showHtmlFragment $ (table $ concatHtml $ map (tr . go . toNorm) as) ! [border 1])
  where go :: Norm -> Html
        go e =  case e of
                  UnitN _         -> td $ stringToHtml "()"
                  BoolN b _       -> td $ stringToHtml (show b)
                  CharN c _       -> td $ stringToHtml [c]
                  IntegerN i _    -> td $ stringToHtml (show i)
                  DoubleN d _     -> td $ stringToHtml (show d)
                  TextN t _       -> td $ stringToHtml (Text.unpack t)
                  TupleN e1 e2 _  -> concatHtml $ map go (e1 : deTuple e2)
                  ListN es _      -> td $ (table $ concatHtml $ map (tr . go) es) ! [border 1]

deTuple :: Norm -> [Norm]
deTuple (TupleN e1 e2 _) = e1 : deTuple e2
deTuple n = [n]