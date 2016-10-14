module Database.DSH.SL.Render.Dot(renderSLDot) where

import           Control.Monad.Reader
import qualified Data.Foldable                  as F
import qualified Data.IntMap                    as Map
import           Data.List
import qualified Data.List.NonEmpty             as N
import           Prelude                        hiding ((<$>))

import           Text.PrettyPrint.ANSI.Leijen

import qualified Database.Algebra.Dag           as Dag
import           Database.Algebra.Dag.Common    as C

import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type
import           Database.DSH.Common.VectorLang
import           Database.DSH.SL.Lang

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

bracketList :: (a -> Doc) -> [a] -> Doc
bracketList f = brackets . hsep . punctuate comma . map f

renderColName :: L.ColName -> Doc
renderColName (L.ColName c) = text c

renderCol :: (L.ColName, ScalarType) -> Doc
renderCol (c, t) = renderColName c <> text "::" <> renderColumnType t

renderJoinConjunct :: L.JoinConjunct VectorExpr -> Doc
renderJoinConjunct (L.JoinConjunct e1 o e2) =
    parenthize1 e1 <+> text (pp o) <+> parenthize1 e2

renderJoinPred :: L.JoinPredicate VectorExpr -> Doc
renderJoinPred (L.JoinPred conjs) = brackets
                                    $ hsep
                                    $ punctuate (text "&&")
                                    $ map renderJoinConjunct $ N.toList conjs

renderLambda :: VectorExpr -> Doc
renderLambda e = text "\\x." <> renderExpr e

renderSegments :: VecSegs -> Doc
renderSegments (UnitSeg seg) = renderSegment seg
renderSegments (Segs segs)   = vcat $ map renderSegment $ F.toList segs

renderSegment :: SegD -> Doc
renderSegment s = list $ map pretty $ F.toList s

type Render = Reader (NodeMap [Tag])

renderTags :: [Tag] -> Doc
renderTags = vcat . map text

renderId :: AlgNode -> Doc
renderId n = text "id:" <+> int n

labelDoc :: AlgNode -> String -> Doc -> Render Doc
labelDoc nodeId opName arg = do
    tags <- asks $ Map.findWithDefault [] nodeId
    pure $ renderId nodeId <$> (text opName <> arg) <$> renderTags tags

renderLabel :: AlgNode -> String -> Render Doc
renderLabel nodeId opName = labelDoc nodeId opName empty

renderLabelArg :: AlgNode -> String -> Doc -> Render Doc
renderLabelArg nodeId opName arg = labelDoc nodeId opName (braces arg)

-- | Create the node label from an operator description
opDotLabel :: AlgNode -> SL -> Render Doc
opDotLabel i (UnOp (WinFun (wfun, wspec)) _) = renderLabelArg i "winaggr" (renderWinFun wfun <> comma <+> renderFrameSpec wspec)
opDotLabel i (NullaryOp (Lit (ty, segs))) = renderLabelArg i "lit" (pretty ty <> comma <$> renderSegments segs)
opDotLabel i (NullaryOp (TableRef (n, schema))) = renderLabelArg i "table" arg
  where
    arg  = text n <> text "\n" <> align (bracketList (\c -> renderCol c <> text "\n") cols)
    cols = N.toList $ L.tableCols schema
opDotLabel i (UnOp Unique _) = renderLabel i "unique"
opDotLabel i (UnOp Number _) = renderLabel i "number"
opDotLabel i (UnOp UnboxKey _) = renderLabel i "unboxkey"
opDotLabel i (UnOp Segment _) = renderLabel i "segment"
opDotLabel i (UnOp Unsegment _) = renderLabel i "unsegment"
opDotLabel i (UnOp Reverse _) = renderLabel i "reverse"
opDotLabel i (UnOp R1 _) = renderLabel i "R1"
opDotLabel i (UnOp R2 _) = renderLabel i "R2"
opDotLabel i (UnOp R3 _) = renderLabel i "R3"
opDotLabel i (UnOp (Project e) _) = renderLabelArg i "project" arg
  where
    arg = renderLambda e
opDotLabel i (UnOp (Select e) _) = renderLabelArg i "select" (renderLambda e)
opDotLabel i (UnOp (GroupAggr (g, a)) _) = renderLabelArg i "groupaggr" (renderLambda g <+> bracketList renderAggrFun [a])
opDotLabel i (BinOp (Fold a) _ _) = renderLabelArg i "fold" (renderAggrFun a)
opDotLabel i (UnOp (Sort e) _) = renderLabelArg i "sort" (renderLambda e)
opDotLabel i (UnOp (Group e) _) = renderLabelArg i "group" (renderLambda e)
opDotLabel i (BinOp ReplicateNest _ _) = renderLabel i "replicatenest"
opDotLabel i (BinOp ReplicateScalar _ _) = renderLabel i "replicatescalar"
opDotLabel i (BinOp UnboxSng _ _) = renderLabel i "unboxsng"
opDotLabel i (BinOp AppSort _ _) = renderLabel i "appsort"
opDotLabel i (BinOp AppKey _ _) = renderLabel i "appkey"
opDotLabel i (BinOp AppFilter _ _) = renderLabel i "appfilter"
opDotLabel i (BinOp AppRep _ _) = renderLabel i "apprep"
opDotLabel i (BinOp Append _ _) = renderLabel i "append"
opDotLabel i (BinOp Align _ _) = renderLabel i "align"
opDotLabel i (BinOp Zip _ _) = renderLabel i "zip"
opDotLabel i (BinOp CartProduct _ _) = renderLabel i "cartproduct"
opDotLabel i (BinOp ReplicateVector _ _) = renderLabel i "replicatevector"
opDotLabel i (BinOp (ThetaJoin p) _ _) =
  renderLabelArg i "thetajoin" (renderJoinPred p)
opDotLabel i (BinOp (NestJoin p) _ _) =
  renderLabelArg i "nestjoin" (renderJoinPred p)
opDotLabel i (BinOp (SemiJoin p) _ _) =
  renderLabelArg i "semijoin" (renderJoinPred p)
opDotLabel i (BinOp (AntiJoin p) _ _) =
  renderLabelArg i "antijoin" (renderJoinPred p)
opDotLabel i (BinOp (GroupJoin (p, as)) _ _) =
    renderLabelArg i "groupjoin" arg
  where
    arg = renderJoinPred p <+> bracketList renderAggrFun (N.toList $ L.getNE as)
opDotLabel i (TerOp Combine _ _ _) = renderLabel i "combine"

opDotColor :: SL -> DotColor
opDotColor (BinOp CartProduct _ _)    = DCRed
opDotColor (BinOp ReplicateVector _ _) = DCRed
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
opDotColor (BinOp (Fold _) _ _)        = DCCrimson
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

constructDotNode :: [AlgNode] -> NodeMap [Tag] -> (AlgNode, SL) -> DotNode
constructDotNode rootNodes ts (n, op) =
    if elem n rootNodes then
        DotNode n l c (Just Dashed)
    else
        DotNode n l c Nothing
  where
    l = escapeLabel $ pp $ runReader (opDotLabel n op) ts
    c = opDotColor op

-- | Create an abstract Dot edge
constructDotEdge :: (AlgNode, AlgNode) -> DotEdge
constructDotEdge = uncurry DotEdge

-- | extract the operator descriptions and list of edges from a DAG
-- FIXME no apparent reason to use topological ordering here
extractGraphStructure :: Dag.AlgebraDag SL
                     -> ([(AlgNode, SL)], [(AlgNode, AlgNode)])
extractGraphStructure d = (operators, childs)
  where
    nodes = Dag.topsort d
    operators = zip nodes $ map (flip Dag.operator d) nodes
    childs = concat $ map (\(n, op) -> zip (repeat n) (Dag.opChildren op)) operators

-- | Render an SL plan into a dot file (GraphViz).
renderSLDot :: NodeMap [Tag] -> [AlgNode] -> NodeMap SL -> String
renderSLDot ts roots m = pp $ renderDot dotNodes dotEdges
  where
    (opLabels, edges) = extractGraphStructure d
    d = Dag.mkDag m roots
    dotNodes = map (constructDotNode roots ts) opLabels
    dotEdges = map constructDotEdge edges
