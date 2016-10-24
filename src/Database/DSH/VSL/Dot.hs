module Database.DSH.VSL.Dot
    ( renderVSLDot
    ) where

import qualified Data.Foldable                  as F
import qualified Data.IntMap                    as Map
import           Data.List
import qualified Data.List.NonEmpty             as N
import           Prelude                        hiding ((<$>))

import           Text.PrettyPrint.ANSI.Leijen

import qualified Database.Algebra.Dag           as Dag
import           Database.Algebra.Dag.Common    as C

import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type
import           Database.DSH.Common.VectorLang
import           Database.DSH.VSL.Lang

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

renderAggrFun :: Pretty e => AggrFun e -> Doc
renderAggrFun (AggrSum t c)         = renderFun (text "sum" <> char '_' <> renderColumnType t)
                                                [pretty c]
renderAggrFun (AggrMin c)           = renderFun (text "min") [pretty c]
renderAggrFun (AggrMax c)           = renderFun (text "max") [pretty c]
renderAggrFun (AggrAvg c)           = renderFun (text "avg") [pretty c]
renderAggrFun (AggrAny c)           = renderFun (text "any") [pretty c]
renderAggrFun (AggrAll c)           = renderFun (text "all") [pretty c]
renderAggrFun AggrCount             = renderFun (text "count") []
renderAggrFun (AggrCountDistinct c) = renderFun (text "countDistinct") [pretty c]

renderWinFun :: Pretty e => WinFun e -> Doc
renderWinFun (WinSum c)        = renderFun (text "sum") [pretty c]
renderWinFun (WinMin c)        = renderFun (text "min") [pretty c]
renderWinFun (WinMax c)        = renderFun (text "max") [pretty c]
renderWinFun (WinAvg c)        = renderFun (text "avg") [pretty c]
renderWinFun (WinAny c)        = renderFun (text "any") [pretty c]
renderWinFun (WinAll c)        = renderFun (text "all") [pretty c]
renderWinFun (WinFirstValue c) = renderFun (text "first_value") [pretty c]
renderWinFun WinCount          = renderFun (text "count") []

renderColumnType :: ScalarType -> Doc
renderColumnType = text . show

bracketList :: (a -> Doc) -> [a] -> Doc
bracketList f = brackets . hsep . punctuate comma . map f

renderColName :: L.ColName -> Doc
renderColName (L.ColName c) = text c

renderCol :: (L.ColName, ScalarType) -> Doc
renderCol (c, t) = renderColName c <> text "::" <> renderColumnType t

renderJoinConjunct :: Pretty e => L.JoinConjunct e -> Doc
renderJoinConjunct (L.JoinConjunct e1 o e2) =
    pretty e1 <+> text (pp o) <+> pretty e2

renderJoinPred :: Pretty e => L.JoinPredicate e -> Doc
renderJoinPred (L.JoinPred conjs) = brackets
                                    $ hsep
                                    $ punctuate (text "&&")
                                    $ map renderJoinConjunct $ N.toList conjs

renderSegments :: VecSegs -> Doc
renderSegments (UnitSeg seg) = renderSegment seg
renderSegments (Segs segs)   = vcat $ map renderSegment $ F.toList segs

renderSegment :: SegD -> Doc
renderSegment s = list $ map pretty $ F.toList s

renderSegLookup :: SegmentLookup -> String
renderSegLookup Direct = "M"
renderSegLookup Unit   = "U"

-- | Create the node label from an operator description
opDotLabel :: (Pretty e, Pretty r) => NodeMap [Tag] -> AlgNode -> VSLOp r e -> Doc
opDotLabel tm i (UnOp (WinFun (wfun, wspec)) _) = labelToDoc i "winaggr"
    (renderWinFun wfun <> comma <+> renderFrameSpec wspec)
    (lookupTags i tm)
opDotLabel tm i (NullaryOp (Lit (ty, segs))) = labelToDoc i "lit"
        (pretty ty <> comma <$> renderSegments segs) (lookupTags i tm)
opDotLabel tm i (NullaryOp (TableRef (n, schema))) =
    labelToDoc i "table"
                 (text n <> text "\n"
                  <> align (bracketList (\c -> renderCol c <> text "\n")
                                        (N.toList $ L.tableCols schema)))
                 (lookupTags i tm)
opDotLabel tm i (UnOp Distinct _) = labelToDoc i "unique" empty (lookupTags i tm)
opDotLabel tm i (UnOp Number _) = labelToDoc i "number" empty (lookupTags i tm)
opDotLabel tm i (UnOp MergeMap _) = labelToDoc i "mergemap" empty (lookupTags i tm)
opDotLabel tm i (UnOp Segment _) = labelToDoc i "segment" empty (lookupTags i tm)
opDotLabel tm i (UnOp Unsegment _) = labelToDoc i "unsegment" empty (lookupTags i tm)
opDotLabel tm i (UnOp UnitMap _) = labelToDoc i "unitmap" empty (lookupTags i tm)
opDotLabel tm i (UnOp UpdateUnit _) = labelToDoc i "updateunit" empty (lookupTags i tm)
opDotLabel tm i (UnOp Reverse _) = labelToDoc i "reverse" empty (lookupTags i tm)
opDotLabel tm i (UnOp R1 _) = labelToDoc i "R1" empty (lookupTags i tm)
opDotLabel tm i (UnOp R2 _) = labelToDoc i "R2" empty (lookupTags i tm)
opDotLabel tm i (UnOp R3 _) = labelToDoc i "R3" empty (lookupTags i tm)
opDotLabel tm i (UnOp (Project e) _) = labelToDoc i "project" pLabel (lookupTags i tm)
  where pLabel = pretty e
opDotLabel tm i (UnOp (Select e) _) = labelToDoc i "select" (pretty e) (lookupTags i tm)
opDotLabel tm i (UnOp (GroupAggr (g, a)) _) = labelToDoc i "groupaggr" (pretty g <+> bracketList renderAggrFun [a]) (lookupTags i tm)
opDotLabel tm i (UnOp (Fold a) _) = labelToDoc i "aggrseg" (renderAggrFun a) (lookupTags i tm)
opDotLabel tm i (UnOp (Sort e) _) = labelToDoc i "sort" (pretty e) (lookupTags i tm)
opDotLabel tm i (UnOp (Group e) _) = labelToDoc i "group" (pretty e) (lookupTags i tm)
opDotLabel tm i (BinOp ReplicateSeg _ _) = labelToDoc i "replicatenest" empty (lookupTags i tm)
opDotLabel tm i (BinOp ReplicateScalar _ _) = labelToDoc i "replicatescalar" empty (lookupTags i tm)
opDotLabel tm i (BinOp Materialize _ _) = labelToDoc i "materialize" empty (lookupTags i tm)
opDotLabel tm i (BinOp UpdateMap _ _) = labelToDoc i "updatemap" empty (lookupTags i tm)
opDotLabel tm i (BinOp UnboxSng _ _) = labelToDoc i "unboxsng" empty (lookupTags i tm)
opDotLabel tm i (BinOp (UnboxDefault vs) _ _) = labelToDoc i "unboxdefault" (bracketList pretty $ N.toList vs) (lookupTags i tm)
opDotLabel tm i (BinOp Append _ _) = labelToDoc i "append" empty (lookupTags i tm)
opDotLabel tm i (BinOp Align _ _) = labelToDoc i "align" empty (lookupTags i tm)
opDotLabel tm i (BinOp Zip _ _) = labelToDoc i "zip" empty (lookupTags i tm)
opDotLabel tm i (BinOp CartProduct _ _) = labelToDoc i "cartproduct" empty (lookupTags i tm)
opDotLabel tm i (BinOp (ThetaJoin (l1, l2, p)) _ _) =
  labelToDoc i ("thetajoin" ++ renderSegLookup l1 ++ renderSegLookup l2) (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (NestJoin (l1, l2, p)) _ _) =
  labelToDoc i ("nestjoin" ++ renderSegLookup l1 ++ renderSegLookup l2) (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (AntiJoin (l1, l2, p)) _ _) =
  labelToDoc i  ("antijoin" ++ renderSegLookup l1 ++ renderSegLookup l2)(renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (SemiJoin (l1, l2, p)) _ _) =
  labelToDoc i ("semijoin" ++ renderSegLookup l1 ++ renderSegLookup l2) (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (GroupJoin (l1, l2, p, as)) _ _) =
  labelToDoc i ("groupjoin" ++ renderSegLookup l1 ++ renderSegLookup l2) (renderJoinPred p <+> bracketList renderAggrFun (N.toList $ L.getNE as)) (lookupTags i tm)
opDotLabel tm i (TerOp Combine _ _ _) = labelToDoc i "combine" empty (lookupTags i tm)

opDotColor :: VSLOp r e -> DotColor
opDotColor (BinOp CartProduct _ _)     = DCRed
opDotColor (BinOp Materialize _ _)     = DCSalmon
opDotColor (BinOp (ThetaJoin _) _ _)   = DCGreen
opDotColor (BinOp (NestJoin _) _ _)    = DCGreen
opDotColor (BinOp (SemiJoin _) _ _)    = DCGreen
opDotColor (BinOp (AntiJoin _) _ _)    = DCGreen
opDotColor (BinOp (GroupJoin _) _ _)   = DCGreen
opDotColor (UnOp (Sort _) _)           = DCTomato
opDotColor (UnOp (Group _) _)          = DCTomato
opDotColor (BinOp UnboxSng _ _)        = DCTan
opDotColor (BinOp ReplicateSeg _ _)    = DCTan
opDotColor (BinOp ReplicateScalar _ _) = DCTan
opDotColor (BinOp Align _ _)           = DCTan
opDotColor (TerOp Combine _ _ _)       = DCDodgerBlue
opDotColor (UnOp (Select _) _)         = DCLightSkyBlue
opDotColor (UnOp (Fold _) _)        = DCCrimson
opDotColor (UnOp (WinFun _) _)         = DCTomato
opDotColor (UnOp (GroupAggr (_, _)) _) = DCTomato
opDotColor (UnOp (Project _) _)        = DCLightSkyBlue
opDotColor (BinOp UpdateMap _ _)       = DCCyan
opDotColor (UnOp UnitMap _)            = DCCornFlowerBlue
opDotColor (UnOp MergeMap _)           = DCCornFlowerBlue
opDotColor (UnOp UpdateUnit _)         = DCCornFlowerBlue
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
              | DCBlueViolet
              | DCHotPink
              | DCBrown
              | DCCyan
              | DCCornFlowerBlue

renderColor :: DotColor -> Doc
renderColor DCTomato         = text "tomato"
renderColor DCSalmon         = text "salmon"
renderColor DCGray           = text "gray"
renderColor DimDCGray        = text "dimgray"
renderColor DCGold           = text "gold"
renderColor DCTan            = text "tan"
renderColor DCRed            = text "red"
renderColor DCCrimson        = text "crimson"
renderColor DCGreen          = text "green"
renderColor DCSeaGreen       = text "seagreen"
renderColor DCYelloGreen     = text "yellowgreen"
renderColor DCSienna         = text "sienna"
renderColor DCBeige          = text "beige"
renderColor DCDodgerBlue     = text "dodgerblue"
renderColor DCLightSkyBlue   = text "lightskyblue"
renderColor DCHotPink        = text "hotpink"
renderColor DCBrown          = text "brown"
renderColor DCCyan           = text "cyan"
renderColor DCBlueViolet     = text "blueviolet"
renderColor DCCornFlowerBlue = text "cornflowerblue"

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
constructDotNode :: (Pretty r, Pretty e)
                 => [AlgNode]
                 -> NodeMap [Tag]
                 -> (AlgNode, VSL r e)
                 -> DotNode
constructDotNode rootNodes ts (n, op) =
    if elem n rootNodes then
        DotNode n l c (Just Dashed)
    else
        DotNode n l c Nothing
  where
    l = escapeLabel $ pp $ opDotLabel ts n $ unVSL op
    c = opDotColor $ unVSL op

-- | Create an abstract Dot edge
constructDotEdge :: (AlgNode, AlgNode) -> DotEdge
constructDotEdge = uncurry DotEdge

-- | extract the operator descriptions and list of edges from a DAG
-- FIXME no apparent reason to use topological ordering here
extractGraphStructure :: Ordish r e
                      => Dag.AlgebraDag (VSL r e)
                      -> ([(AlgNode, VSL r e)], [(AlgNode, AlgNode)])
extractGraphStructure d = (operators, childs)
  where
    nodes = Dag.topsort d
    operators = zip nodes $ map (flip Dag.operator d) nodes
    childs = concat $ map (\(n, op) -> zip (repeat n) (Dag.opChildren op)) operators

-- | Render an SL plan into a dot file (GraphViz).
renderVSLDot :: (Ord r, Ord e, Show r, Show e, Pretty r, Pretty e)
             => NodeMap [Tag]
             -> [AlgNode]
             -> NodeMap (VSL r e)
             -> String
renderVSLDot ts roots m = pp $ renderDot dotNodes dotEdges
  where
    (opLabels, edges) = extractGraphStructure d
    d = Dag.mkDag m roots
    dotNodes = map (constructDotNode roots ts) opLabels
    dotEdges = map constructDotEdge edges
