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
xhtmlExportHandle handle as = IO.hPutStr handle (showHtmlFragment $ go 0 0 $ toNorm as)
  where go :: Integer -> Integer -> Norm -> Html
        go tl rl e =  case e of
                        UnitN _         -> (td $ stringToHtml $ "()")           ! [tdAttr tl rl]
                        BoolN b _       -> (td $ stringToHtml $ show b)         ! [tdAttr tl rl]
                        CharN c _       -> (td $ stringToHtml $ [c])            ! [tdAttr tl rl]
                        IntegerN i _    -> (td $ stringToHtml $ show i)         ! [tdAttr tl rl]
                        DoubleN d _     -> (td $ stringToHtml $ show d)         ! [tdAttr tl rl]
                        TextN t _       -> (td $ stringToHtml $ Text.unpack t)  ! [tdAttr tl rl]
                        TupleN e1 e2 _  -> (concatHtml $ map (go tl rl) (e1 : deTuple e2))
                        ListN es _      -> td $ (table  $ concatHtml
                                                        $ map (\(l1,e1) -> tr (go (tl + 1) l1 e1))
                                                        $ zip [0 ..] es
                                                ) ! [tableAttr]

        tdAttr :: Integer -> Integer -> HtmlAttr
        tdAttr tl rl = case (odd tl,odd rl) of
                         (False,False) -> strAttr "style" "text-align:center; min-width:20px; padding:5px; background-color:#EEE;"
                         (False,True)  -> strAttr "style" "text-align:center; min-width:20px; padding:5px; background-color:#CCC;"
                         (True,False)  -> strAttr "style" "text-align:center; min-width:20px; padding:5px; background-color:#DDD;"
                         (True,True)   -> strAttr "style" "text-align:center; min-width:20px; padding:5px; background-color:#E9E9E9;"

        tableAttr :: HtmlAttr
        tableAttr = strAttr "style" "border-spacing:5px;"


deTuple :: Norm -> [Norm]
deTuple (TupleN e1 e2 _) = e1 : deTuple e2
deTuple n = [n]