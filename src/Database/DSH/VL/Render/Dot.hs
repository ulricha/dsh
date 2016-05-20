module Database.DSH.VL.Render.Dot(renderVLDot) where

import qualified Data.Foldable                as F
import qualified Data.IntMap                  as Map
import           Data.List
import qualified Data.List.NonEmpty           as N
import           Prelude                      hiding ((<$>))

import           Text.PrettyPrint.ANSI.Leijen

import qualified Database.Algebra.Dag         as Dag
import           Database.Algebra.Dag.Common  as C

import qualified Database.DSH.Common.Lang     as L
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type
import           Database.DSH.VL.Lang

nodeToDoc :: AlgNode -> Doc
nodeToDoc n = text "id:" <+> int n

tagsToDoc :: [Tag] -> Doc
tagsToDoc ts = vcat $ map text ts

labelToDoc :: AlgNode -> String -> Doc -> [Tag] -> Doc
labelToDoc n s as ts = nodeToDoc n <$> (text s <> parens as) <$> tagsToDoc (nub ts)

lookupTags :: AlgNode -> NodeMap [Tag] -> [Tag]
lookupTags = Map.findWithDefault []

renderFun :: Doc -> [Doc] -> Doc
renderFun name args = name <> parens (hsep $ punctuate comma args)

renderFrameSpec :: FrameSpec -> Doc
renderFrameSpec FAllPreceding   = text "allprec"
renderFrameSpec (FNPreceding n) = int n <+> text "prec"

renderAggrFun :: AggrFun -> Doc
renderAggrFun (AggrSum t c)         = renderFun (text "sum" <> char '_' <> renderColumnType t)
                                                [renderExpr c]
renderAggrFun (AggrMin c)           = renderFun (text "min") [renderExpr c]
renderAggrFun (AggrMax c)           = renderFun (text "max") [renderExpr c]
renderAggrFun (AggrAvg c)           = renderFun (text "avg") [renderExpr c]
renderAggrFun (AggrAny c)           = renderFun (text "any") [renderExpr c]
renderAggrFun (AggrAll c)           = renderFun (text "all") [renderExpr c]
renderAggrFun AggrCount             = renderFun (text "count") []
renderAggrFun (AggrCountDistinct c) = renderFun (text "countDistinct") [renderExpr c]

renderWinFun :: WinFun -> Doc
renderWinFun (WinSum c)        = renderFun (text "sum") [renderExpr c]
renderWinFun (WinMin c)        = renderFun (text "min") [renderExpr c]
renderWinFun (WinMax c)        = renderFun (text "max") [renderExpr c]
renderWinFun (WinAvg c)        = renderFun (text "avg") [renderExpr c]
renderWinFun (WinAny c)        = renderFun (text "any") [renderExpr c]
renderWinFun (WinAll c)        = renderFun (text "all") [renderExpr c]
renderWinFun (WinFirstValue c) = renderFun (text "first_value") [renderExpr c]
renderWinFun WinCount          = renderFun (text "count") []

renderColumnType :: ScalarType -> Doc
renderColumnType = text . show

renderData :: [[L.ScalarVal]] -> Doc
renderData [] = brackets empty
renderData xs = flip (<>) semi $ sep $ punctuate semi $ map renderRow xs

renderRow :: [L.ScalarVal] -> Doc
renderRow = hcat . punctuate comma . map pretty

bracketList :: (a -> Doc) -> [a] -> Doc
bracketList f = brackets . hsep . punctuate comma . map f

renderColName :: L.ColName -> Doc
renderColName (L.ColName c) = text c

renderCol :: (L.ColName, ScalarType) -> Doc
renderCol (c, t) = renderColName c <> text "::" <> renderColumnType t

renderProj :: Doc -> Expr -> Doc
renderProj d e = d <> colon <> renderExpr e

renderJoinConjunct :: L.JoinConjunct Expr -> Doc
renderJoinConjunct (L.JoinConjunct e1 o e2) =
    parenthize1 e1 <+> text (pp o) <+> parenthize1 e2

renderJoinPred :: L.JoinPredicate Expr -> Doc
renderJoinPred (L.JoinPred conjs) = brackets
                                    $ hsep
                                    $ punctuate (text "&&")
                                    $ map renderJoinConjunct $ N.toList conjs

renderExpr :: Expr -> Doc
renderExpr (BinApp op e1 e2) = parenthize1 e1 <+> text (pp op) <+> parenthize1 e2
renderExpr (UnApp op e)      = text (pp op) <+> parens (renderExpr e)
renderExpr (Constant val)    = pretty val
renderExpr (Column c)        = text "col" <> int c
renderExpr (If c t e)        = text "if"
                                 <+> renderExpr c
                                 <+> text "then"
                                 <+> renderExpr t
                                 <+> text "else"
                                 <+> renderExpr e

parenthize1 :: Expr -> Doc
parenthize1 e@(Constant _) = renderExpr e
parenthize1 e@(Column _)   = renderExpr e
parenthize1 e@BinApp{}     = parens $ renderExpr e
parenthize1 e@UnApp{}      = parens $ renderExpr e
parenthize1 e@If{}         = renderExpr e

renderSegments :: Segments -> Doc
renderSegments (UnitSeg cols) = renderColumns cols
renderSegments (Segs segs)    = vcat $ map renderSegment segs

renderSegment :: Segment -> Doc
renderSegment s = brackets $ renderColumns $ segCols s

renderColumns :: [Column] -> Doc
renderColumns cols = renderData $ transpose $ map F.toList $ F.toList cols

-- | Create the node label from an operator description
opDotLabel :: NodeMap [Tag] -> AlgNode -> VL -> Doc
opDotLabel tm i (UnOp (WinFun (wfun, wspec)) _) = labelToDoc i "WinAggr"
    (renderWinFun wfun <> comma <+> renderFrameSpec wspec)
    (lookupTags i tm)
opDotLabel tm i (NullaryOp (Lit (tys, frame, segs))) = labelToDoc i "LIT"
        (bracketList renderColumnType tys <> comma
        <$> text "frame: " <> int (frameLen frame) <> comma
        <$> renderSegments segs) (lookupTags i tm)
opDotLabel tm i (NullaryOp (TableRef (n, schema))) =
    labelToDoc i "TableScan"
                 (text n <> text "\n"
                  <> align (bracketList (\c -> renderCol c <> text "\n")
                                        (N.toList $ L.tableCols schema)))
                 (lookupTags i tm)
opDotLabel tm i (UnOp Unique _) = labelToDoc i "unique" empty (lookupTags i tm)
opDotLabel tm i (UnOp Number _) = labelToDoc i "number" empty (lookupTags i tm)
opDotLabel tm i (UnOp UnboxKey _) = labelToDoc i "unboxkey" empty (lookupTags i tm)
opDotLabel tm i (UnOp Segment _) = labelToDoc i "segment" empty (lookupTags i tm)
opDotLabel tm i (UnOp Unsegment _) = labelToDoc i "unsegment" empty (lookupTags i tm)
opDotLabel tm i (UnOp Nest _) = labelToDoc i "nest" empty (lookupTags i tm)
opDotLabel tm i (UnOp Reverse _) = labelToDoc i "reverse" empty (lookupTags i tm)
opDotLabel tm i (UnOp R1 _) = labelToDoc i "R1" empty (lookupTags i tm)
opDotLabel tm i (UnOp R2 _) = labelToDoc i "R2" empty (lookupTags i tm)
opDotLabel tm i (UnOp R3 _) = labelToDoc i "R3" empty (lookupTags i tm)
opDotLabel tm i (UnOp (Project pCols) _) =
  labelToDoc i "project" pLabel (lookupTags i tm)
  where pLabel = valCols
        valCols = bracketList (\(j, p) -> renderProj (itemLabel j) p) $ zip ([1..] :: [Int]) pCols
        itemLabel j = (text "i") <> (int j)
opDotLabel tm i (UnOp (Select e) _) = labelToDoc i "select" (renderExpr e) (lookupTags i tm)
opDotLabel tm i (UnOp (GroupAggr (g, as)) _) = labelToDoc i "groupaggr" (bracketList renderExpr g <+> bracketList renderAggrFun (N.toList as)) (lookupTags i tm)
opDotLabel tm i (UnOp (Aggr as) _) = labelToDoc i "aggr" (bracketList renderAggrFun (N.toList as)) (lookupTags i tm)
opDotLabel tm i (BinOp (AggrSeg a) _ _) = labelToDoc i "aggrseg" (renderAggrFun a) (lookupTags i tm)
opDotLabel tm i (UnOp (Sort cols) _) = labelToDoc i "sort" (bracketList renderExpr cols) (lookupTags i tm)
opDotLabel tm i (UnOp (Group cols) _) = labelToDoc i "group" (bracketList renderExpr cols) (lookupTags i tm)
opDotLabel tm i (BinOp ReplicateNest _ _) = labelToDoc i "replicatenest" empty (lookupTags i tm)
opDotLabel tm i (BinOp ReplicateScalar _ _) = labelToDoc i "replicatescalar" empty (lookupTags i tm)
opDotLabel tm i (BinOp UnboxSng _ _) = labelToDoc i "unboxsng" empty (lookupTags i tm)
opDotLabel tm i (BinOp AppSort _ _) = labelToDoc i "appsort" empty (lookupTags i tm)
opDotLabel tm i (BinOp AppKey _ _) = labelToDoc i "appkey" empty (lookupTags i tm)
opDotLabel tm i (BinOp AppFilter _ _) = labelToDoc i "appfilter" empty (lookupTags i tm)
opDotLabel tm i (BinOp AppRep _ _) = labelToDoc i "apprep" empty (lookupTags i tm)
opDotLabel tm i (BinOp Append _ _) = labelToDoc i "append" empty (lookupTags i tm)
opDotLabel tm i (BinOp Align _ _) = labelToDoc i "align" empty (lookupTags i tm)
opDotLabel tm i (BinOp Zip _ _) = labelToDoc i "zip" empty (lookupTags i tm)
opDotLabel tm i (BinOp CartProduct _ _) = labelToDoc i "cartproduct" empty (lookupTags i tm)
opDotLabel tm i (BinOp NestProduct _ _) = labelToDoc i "nestproduct" empty (lookupTags i tm)
opDotLabel tm i (BinOp (ThetaJoin p) _ _) =
  labelToDoc i "thetajoin" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (NestJoin p) _ _) =
  labelToDoc i "nestjoin" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (SemiJoin p) _ _) =
  labelToDoc i "semijoin" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (AntiJoin p) _ _) =
  labelToDoc i "antijoin" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (GroupJoin (p, as)) _ _) =
  labelToDoc i "groupjoin" (renderJoinPred p <+> bracketList renderAggrFun (N.toList $ L.getNE as)) (lookupTags i tm)
opDotLabel tm i (TerOp Combine _ _ _) = labelToDoc i "combine" empty (lookupTags i tm)

opDotColor :: VL -> DotColor
opDotColor (BinOp CartProduct _ _)    = DCRed
opDotColor (BinOp NestProduct _ _)    = DCRed
opDotColor (BinOp (ThetaJoin _) _ _)  = DCGreen
opDotColor (BinOp (NestJoin _) _ _)   = DCGreen
opDotColor (BinOp (SemiJoin _) _ _)   = DCGreen
opDotColor (BinOp (AntiJoin _) _ _)   = DCGreen
opDotColor (BinOp (GroupJoin _) _ _)   = DCGreen
opDotColor (UnOp (Sort _) _)          = DCTomato
opDotColor (UnOp (Group _) _)         = DCTomato
opDotColor (BinOp UnboxSng _ _)        = DCTan
opDotColor (BinOp AppSort _ _)         = DCTan
opDotColor (BinOp AppKey _ _)          = DCTan
opDotColor (BinOp AppFilter _ _)       = DCTan
opDotColor (BinOp AppRep _ _)          = DCTan
opDotColor (BinOp ReplicateNest _ _)   = DCTan
opDotColor (BinOp ReplicateScalar _ _) = DCTan
opDotColor (BinOp Align _ _)           = DCTan
opDotColor (TerOp Combine _ _ _)       = DCDodgerBlue
opDotColor (UnOp (Select _) _)         = DCLightSkyBlue
opDotColor (UnOp (Aggr _) _)           = DCCrimson
opDotColor (BinOp (AggrSeg _) _ _)     = DCCrimson
opDotColor (UnOp (WinFun _) _)         = DCTomato
opDotColor (UnOp (GroupAggr (_, _)) _) = DCTomato
opDotColor (UnOp (Project _) _)        = DCLightSkyBlue
opDotColor _                           = DCGray

-- Dot colors
data DotColor = DCTomato
              | DCSalmon
              | DCGray
              | DimDCGray
              | DCGold
              | DCTan
              | DCRed
              | DCCrimson
              | DCGreen
              | DCSeaGreen
              | DCYelloGreen
              | DCSienna
              | DCBeige
              | DCDodgerBlue
              | DCLightSkyBlue
              | DCHotPink

renderColor :: DotColor -> Doc
renderColor DCTomato       = text "tomato"
renderColor DCSalmon       = text "salmon"
renderColor DCGray         = text "gray"
renderColor DimDCGray      = text "dimgray"
renderColor DCGold         = text "gold"
renderColor DCTan          = text "tan"
renderColor DCRed          = text "red"
renderColor DCCrimson      = text "crimson"
renderColor DCGreen        = text "green"
renderColor DCSeaGreen     = text "seagreen"
renderColor DCYelloGreen   = text "yellowgreen"
renderColor DCSienna       = text "sienna"
renderColor DCBeige        = text "beige"
renderColor DCDodgerBlue   = text "dodgerblue"
renderColor DCLightSkyBlue = text "lightskyblue"
renderColor DCHotPink      = text "hotpink"

escapeLabel :: String -> String
escapeLabel s = concatMap escapeChar s

escapeChar :: Char -> [Char]
escapeChar '\n' = ['\\', 'n']
escapeChar '\\' = ['\\', '\\']
escapeChar '\"' = ['\\', '"']
escapeChar c = [c]

-- Type of Dot style options
data DotStyle = Dashed

-- label of Dot nodes
type DotLabel = String

-- id of Dot nodes
type DotNodeID = Int

-- Type of Dot nodes
data DotNode = DotNode DotNodeID DotLabel DotColor (Maybe DotStyle)

-- Type of Dot edges
data DotEdge = DotEdge DotNodeID DotNodeID

-- Generate the preamble of a Dot file
preamble :: Doc
preamble = graphAttributes <$> nodeAttributes
    where nodeAttributes = text "node" <+> (brackets $ text "style=filled" <> comma <+> text "shape=box") <> semi
          graphAttributes = text "ordering=out;"

renderDotNode :: DotNode -> Doc
renderDotNode (DotNode n l c s) =
    int n
    <+> (brackets $ (((text "label=") <> (dquotes $ text l))
                     <> comma
                     <+> (text "color=") <> (renderColor c)
                     <> styleDoc))
    <> semi
  where
    styleDoc = case s of
                  Just Dashed -> comma <+> text "style=dashed"
                  Nothing     -> empty

renderDotEdge :: DotEdge -> Doc
renderDotEdge (DotEdge u v) = int u <+> text "->" <+> int v <> semi

-- | Render a Dot document from the preamble, nodes and edges
renderDot :: [DotNode] -> [DotEdge] -> Doc
renderDot ns es = text "digraph" <> (braces $ preamble <$> nodeSection <$> edgeSection)
  where
    nodeSection = vcat $ map renderDotNode ns
    edgeSection = vcat $ map renderDotEdge es

-- | Create an abstract Dot node from an X100 operator description
constructDotNode :: [AlgNode] -> NodeMap [Tag] -> (AlgNode, VL) -> DotNode
constructDotNode rootNodes ts (n, op) =
    if elem n rootNodes then
        DotNode n l c (Just Dashed)
    else
        DotNode n l c Nothing
  where
    l = escapeLabel $ pp $ opDotLabel ts n op
    c = opDotColor op

-- | Create an abstract Dot edge
constructDotEdge :: (AlgNode, AlgNode) -> DotEdge
constructDotEdge = uncurry DotEdge

-- | extract the operator descriptions and list of edges from a DAG
-- FIXME no apparent reason to use topological ordering here
extractGraphStructure :: Dag.AlgebraDag VL
                     -> ([(AlgNode, VL)], [(AlgNode, AlgNode)])
extractGraphStructure d = (operators, childs)
  where
    nodes = Dag.topsort d
    operators = zip nodes $ map (flip Dag.operator d) nodes
    childs = concat $ map (\(n, op) -> zip (repeat n) (Dag.opChildren op)) operators

-- | Render an VL plan into a dot file (GraphViz).
renderVLDot :: NodeMap [Tag] -> [AlgNode] -> NodeMap VL -> String
renderVLDot ts roots m = pp $ renderDot dotNodes dotEdges
  where
    (opLabels, edges) = extractGraphStructure d
    d = Dag.mkDag m roots
    dotNodes = map (constructDotNode roots ts) opLabels
    dotEdges = map constructDotEdge edges
