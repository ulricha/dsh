{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VL.Render.Dot(renderVLDot) where

import Prelude hiding ((<$>))
import qualified Data.IntMap                 as Map
import qualified Data.List.NonEmpty          as N
import           Data.List

import           Text.PrettyPrint.ANSI.Leijen

import qualified Database.Algebra.Dag        as Dag
import           Database.Algebra.Dag.Common as C

import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Type
import           Database.DSH.VL.Lang

nodeToDoc :: AlgNode -> Doc
nodeToDoc n = (text "id:") <+> (int n)

tagsToDoc :: [Tag] -> Doc
tagsToDoc ts = vcat $ map text ts

labelToDoc :: AlgNode -> String -> Doc -> [Tag] -> Doc
labelToDoc n s as ts = (nodeToDoc n) <$> ((text s) <> (parens as)) <$> (tagsToDoc $ nub ts)

lookupTags :: AlgNode -> NodeMap [Tag] -> [Tag]
lookupTags n m = Map.findWithDefault [] n m

renderFun :: Doc -> [Doc] -> Doc
renderFun name args = name <> parens (hsep $ punctuate comma args)

renderFrameSpec :: FrameSpec -> Doc
renderFrameSpec FAllPreceding   = text "allprec"
renderFrameSpec (FNPreceding n) = int n <+> text "prec"

renderAggrFun :: AggrFun -> Doc
renderAggrFun (AggrSum t c) = renderFun (text "sum" <> char '_' <> renderColumnType t)
                                        [renderExpr c]
renderAggrFun (AggrMin c)   = renderFun (text "min") [renderExpr c]
renderAggrFun (AggrMax c)   = renderFun (text "max") [renderExpr c]
renderAggrFun (AggrAvg c)   = renderFun (text "avg") [renderExpr c]
renderAggrFun (AggrAny c)   = renderFun (text "any") [renderExpr c]
renderAggrFun (AggrAll c)   = renderFun (text "all") [renderExpr c]
renderAggrFun AggrCount     = renderFun (text "count") []

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

renderData :: [[ScalarVal]] -> Doc
renderData [] = brackets empty
renderData xs = (flip (<>) semi . sep . punctuate semi . map renderRow) xs

renderRow :: [ScalarVal] -> Doc
renderRow = hcat . punctuate comma . map pretty

bracketList :: (a -> Doc) -> [a] -> Doc
bracketList f = brackets . hsep . punctuate comma . map f

renderColName :: ColName -> Doc
renderColName (ColName c) = text c

renderCol :: (ColName, ScalarType) -> Doc
renderCol (c, t) = renderColName c <> text "::" <> renderColumnType t

renderProj :: Doc -> Expr -> Doc
renderProj d e = d <> colon <> renderExpr e

renderJoinConjunct :: JoinConjunct Expr -> Doc
renderJoinConjunct (JoinConjunct e1 o e2) =
    parenthize1 e1 <+> text (pp o) <+> (parenthize1 e2)

renderJoinPred :: JoinPredicate Expr -> Doc
renderJoinPred (JoinPred conjs) = brackets
                                  $ hsep
                                  $ punctuate (text "&&")
                                  $ map renderJoinConjunct $ N.toList conjs

renderExpr :: Expr -> Doc
renderExpr (BinApp op e1 e2) = (parenthize1 e1) <+> (text $ pp op) <+> (parenthize1 e2)
renderExpr (UnApp op e)      = (text $ pp op) <+> (parens $ renderExpr e)
renderExpr (Constant val)    = pretty val
renderExpr (Column c)        = text "col" <> int c
renderExpr (If c t e)        = text "if"
                                 <+> renderExpr c
                                 <+> text "then"
                                 <+> renderExpr t
                                 <+> text "else"
                                 <+> renderExpr e

parenthize1 :: Expr -> Doc
parenthize1 e@(Constant _)   = renderExpr e
parenthize1 e@(Column _)     = renderExpr e
parenthize1 e@(BinApp _ _ _) = parens $ renderExpr e
parenthize1 e@(UnApp _ _)    = parens $ renderExpr e
parenthize1 e@(If _ _ _)     = renderExpr e

-- | Create the node label from an operator description
opDotLabel :: NodeMap [Tag] -> AlgNode -> VL -> Doc
opDotLabel tm i (UnOp (WinFun (wfun, wspec)) _) = labelToDoc i "WinAggr"
    (renderWinFun wfun <> comma <+> renderFrameSpec wspec)
    (lookupTags i tm)
opDotLabel tm i (NullaryOp (SingletonDescr)) = labelToDoc i "SingletonDescr" empty (lookupTags i tm)
opDotLabel tm i (NullaryOp (Lit (_, tys, vals))) = labelToDoc i "LIT"
        (bracketList renderColumnType tys <> comma
        <$> renderData vals) (lookupTags i tm)
opDotLabel tm i (NullaryOp (TableRef (n, schema))) =
    labelToDoc i "TableScan"
                 (text n <> text "\n"
                  <> align (bracketList (\c -> renderCol c <> text "\n")
                                        (N.toList $ tableCols schema)))
                 (lookupTags i tm)
opDotLabel tm i (UnOp Unique _) = labelToDoc i "Unique" empty (lookupTags i tm)
opDotLabel tm i (UnOp UniqueS _) = labelToDoc i "UniqueS" empty (lookupTags i tm)
opDotLabel tm i (UnOp Number _) = labelToDoc i "Number" empty (lookupTags i tm)
opDotLabel tm i (UnOp NumberS _) = labelToDoc i "NumberS" empty (lookupTags i tm)
opDotLabel tm i (UnOp UnboxKey _) = labelToDoc i "UnboxKey" empty (lookupTags i tm)
opDotLabel tm i (UnOp Segment _) = labelToDoc i "Segment" empty (lookupTags i tm)
opDotLabel tm i (UnOp Unsegment _) = labelToDoc i "Unsegment" empty (lookupTags i tm)
opDotLabel tm i (UnOp Reverse _) = labelToDoc i "Reverse" empty (lookupTags i tm)
opDotLabel tm i (UnOp ReverseS _) = labelToDoc i "ReverseS" empty (lookupTags i tm)
opDotLabel tm i (UnOp R1 _) = labelToDoc i "R1" empty (lookupTags i tm)
opDotLabel tm i (UnOp R2 _) = labelToDoc i "R2" empty (lookupTags i tm)
opDotLabel tm i (UnOp R3 _) = labelToDoc i "R3" empty (lookupTags i tm)
opDotLabel tm i (UnOp (Project pCols) _) =
  labelToDoc i "Project" pLabel (lookupTags i tm)
  where pLabel = valCols
        valCols = bracketList (\(j, p) -> renderProj (itemLabel j) p) $ zip ([1..] :: [Int]) pCols
        itemLabel j = (text "i") <> (int j)
opDotLabel tm i (UnOp (Select e) _) = labelToDoc i "Select" (renderExpr e) (lookupTags i tm)
opDotLabel tm i (UnOp (GroupAggr (g, as)) _) = labelToDoc i "GroupAggr" (bracketList renderExpr g <+> bracketList renderAggrFun (N.toList as)) (lookupTags i tm)
opDotLabel tm i (UnOp (Aggr a) _) = labelToDoc i "Aggr" (renderAggrFun a) (lookupTags i tm)
opDotLabel tm i (UnOp (Reshape n) _) =
  labelToDoc i "Reshape" (integer n) (lookupTags i tm)
opDotLabel tm i (BinOp (AggrS a) _ _) = labelToDoc i "AggrS" (renderAggrFun a) (lookupTags i tm)
opDotLabel tm i (UnOp (Sort cols) _) = labelToDoc i "Sort" (bracketList renderExpr cols) (lookupTags i tm)
opDotLabel tm i (UnOp (SortS cols) _) = labelToDoc i "SortS" (bracketList renderExpr cols) (lookupTags i tm)
opDotLabel tm i (UnOp (Group cols) _) = labelToDoc i "Group" (bracketList renderExpr cols) (lookupTags i tm)
opDotLabel tm i (UnOp (GroupS cols) _) = labelToDoc i "GroupS" (bracketList renderExpr cols) (lookupTags i tm)
opDotLabel tm i (BinOp NestProduct _ _) = labelToDoc i "NestProduct" empty (lookupTags i tm)
opDotLabel tm i (BinOp DistLift _ _) = labelToDoc i "DistLift" empty (lookupTags i tm)
opDotLabel tm i (BinOp UnboxScalar _ _) = labelToDoc i "UnboxScalar" empty (lookupTags i tm)
opDotLabel tm i (BinOp AppSort _ _) = labelToDoc i "AppSort" empty (lookupTags i tm)
opDotLabel tm i (BinOp AppKey _ _) = labelToDoc i "AppKey" empty (lookupTags i tm)
opDotLabel tm i (BinOp AppFilter _ _) = labelToDoc i "AppFilter" empty (lookupTags i tm)
opDotLabel tm i (BinOp AppRep _ _) = labelToDoc i "AppRep" empty (lookupTags i tm)
opDotLabel tm i (BinOp Append _ _) = labelToDoc i "Append" empty (lookupTags i tm)
opDotLabel tm i (BinOp AppendS _ _) = labelToDoc i "AppendS" empty (lookupTags i tm)
opDotLabel tm i (BinOp Zip _ _) = labelToDoc i "Zip" empty (lookupTags i tm)
opDotLabel tm i (BinOp Align _ _) = labelToDoc i "Align" empty (lookupTags i tm)
opDotLabel tm i (BinOp ZipS _ _) = labelToDoc i "ZipS" empty (lookupTags i tm)
opDotLabel tm i (BinOp CartProduct _ _) = labelToDoc i "CartProduct" empty (lookupTags i tm)
opDotLabel tm i (BinOp CartProductS _ _) = labelToDoc i "CartProductS" empty (lookupTags i tm)
opDotLabel tm i (BinOp NestProductS _ _) = labelToDoc i "NestProductS" empty (lookupTags i tm)
opDotLabel tm i (BinOp (ThetaJoin p) _ _) =
  labelToDoc i "ThetaJoin" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (NestJoin p) _ _) =
  labelToDoc i "NestJoin" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (ThetaJoinS p) _ _) =
  labelToDoc i "ThetaJoinS" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (NestJoinS p) _ _) =
  labelToDoc i "NestJoinS" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (SemiJoin p) _ _) =
  labelToDoc i "SemiJoin" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (SemiJoinS p) _ _) =
  labelToDoc i "SemiJoinS" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (AntiJoin p) _ _) =
  labelToDoc i "AntiJoin" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (AntiJoinS p) _ _) =
  labelToDoc i "AntiJoinS" (renderJoinPred p) (lookupTags i tm)
opDotLabel tm i (BinOp (GroupJoin (p, a)) _ _) =
  labelToDoc i "GroupJoin" (renderJoinPred p <+> renderAggrFun a) (lookupTags i tm)
opDotLabel tm i (UnOp (ReshapeS n) _) =
  labelToDoc i "ReshapeS" (integer n) (lookupTags i tm)
opDotLabel tm i (UnOp Transpose _) = labelToDoc i "Transpose" empty (lookupTags i tm)
opDotLabel tm i (TerOp Combine _ _ _) = labelToDoc i "Combine" empty (lookupTags i tm)
opDotLabel tm i (BinOp TransposeS _ _) = labelToDoc i "TransposeS" empty (lookupTags i tm)

opDotColor :: VL -> DotColor
opDotColor (BinOp NestProduct _ _)     = DCRed
opDotColor (BinOp CartProduct _ _)     = DCRed
opDotColor (BinOp CartProductS _ _)    = DCRed
opDotColor (BinOp NestProductS _ _)    = DCRed
opDotColor (BinOp (ThetaJoin _) _ _)   = DCGreen
opDotColor (BinOp (NestJoin _) _ _)    = DCGreen
opDotColor (BinOp (ThetaJoinS _) _ _)  = DCGreen
opDotColor (BinOp (NestJoinS _) _ _)   = DCGreen
opDotColor (BinOp (SemiJoin _) _ _)    = DCGreen
opDotColor (BinOp (SemiJoinS _) _ _)   = DCGreen
opDotColor (BinOp (AntiJoin _) _ _)    = DCGreen
opDotColor (BinOp (AntiJoinS _) _ _)   = DCGreen
opDotColor (BinOp (GroupJoin _) _ _)   = DCGreen
opDotColor (BinOp Zip _ _)             = DCYelloGreen
opDotColor (UnOp (Sort _) _)           = DCTomato
opDotColor (UnOp (SortS _) _)          = DCTomato
opDotColor (UnOp (Group _) _)          = DCTomato
opDotColor (UnOp (GroupS _) _)         = DCTomato
opDotColor (BinOp UnboxScalar _ _)     = DCTan
opDotColor (BinOp AppSort _ _)         = DCTan
opDotColor (BinOp AppKey _ _)          = DCTan
opDotColor (BinOp AppFilter _ _)       = DCTan
opDotColor (BinOp AppRep _ _)          = DCTan
opDotColor (BinOp DistLift _ _)        = DCTan
opDotColor (BinOp Align _ _)           = DCTan
opDotColor (TerOp Combine _ _ _)       = DCDodgerBlue
opDotColor (UnOp (Select _) _)         = DCLightSkyBlue
opDotColor (UnOp (Aggr _) _)           = DCCrimson
opDotColor (BinOp (AggrS _) _ _)       = DCCrimson
opDotColor (UnOp (WinFun _) _)         = DCTomato
opDotColor (UnOp (GroupAggr (_, _)) _) = DCTomato
opDotColor (UnOp (Project _) _)        = DCLightSkyBlue
opDotColor (UnOp Transpose _)          = DCHotPink
opDotColor (BinOp TransposeS _ _)      = DCHotPink
opDotColor (UnOp (ReshapeS _) _)       = DCHotPink
opDotColor (UnOp (Reshape _) _)        = DCHotPink
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
