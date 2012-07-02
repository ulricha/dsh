module Language.ParallelLang.VL.Render.Dot (renderVLDot) where
    
import qualified Data.Map as Map
import Data.List

import Text.PrettyPrint
import Language.ParallelLang.VL.Data.VectorLanguage

import Language.ParallelLang.Common.Data.Type
import Database.Algebra.Dag.Common
import qualified Database.Algebra.Dag as Dag
-- import Database.Algebra.X100.Data
-- import Database.Algebra.X100.Render.Common
{-
nodeToDoc :: AlgNode -> Doc
nodeToDoc n = (text "id:") <+> (int n)

tagsToDoc :: [Tag] -> Doc
tagsToDoc ts = vcat $ map text ts

labelToDoc :: AlgNode -> String -> Doc -> [Tag] -> Doc
labelToDoc n s as ts = (nodeToDoc n) $$ ((text s) <> (parens as)) $$ (tagsToDoc $ nub ts)

renderJoinArgs :: [(ColID, ColID)] -> Doc
renderJoinArgs cols = 
    let (k1, k2) = unzip cols
    in bracketList renderColID k1 <> comma <+> bracketList renderColID k2

lookupTags :: AlgNode -> NodeMap [Tag] -> [Tag]
lookupTags n m = Map.findWithDefault [] n m
-}

renderColumnTypes :: [Type] -> Doc
renderColumnTypes [x] = renderColumnType
renderColumnTypes (x:xs) = renderColumnType x <> comma <+> renderColumnTypes xs
renderColumnTypes [] = text "NOTYPE"

renderColumnType :: Type -> Doc
renderColumnType = text . show

renderData :: [[PVal]] -> Doc
renderData [] = empty
renderData xs = (flip (<>) semi . sep . punctuate semi . map renderRow) xs 

renderRow :: [PVal] -> Doc
renderRow = hcat . punctuate comma . map renderTblVal

renderTblVal :: PVal -> Doc
renderTblVal (PInt i) = integer $ fromIntegral i
renderTblVal (PNat i) = integer $ fromIntegral i
renderTblVal (PBool b) = text $ show b
renderTblVal (PString s) = doubleQuotes $ text $ escape s
renderTblVal (PDouble d) = double d
renderTblVal PUnit = text "()"

escape :: String -> String
escape (x@'\\':xs) = '\\':'\\':'\\':x:escape xs
escape (x@'\'':xs) = '\\':x:escape xs
escape (x@'"':xs) = '\\':'\\':x:escape xs
escape (x:xs) = x:escape xs
escape [] = []

bracketList :: (a -> Doc) -> [a] -> Doc
bracketList f = brackets . hsep . punctuate comma . map f

-- create the node label from an operator description
opDotLabel :: NodeMap [Tag] -> AlgNode -> VL -> Doc
opDotLabel tm i (NullaryOp (SingletonDescr)) = labelToDoc i "SingletonDescr" empty (lookupTags i tm)
opDotLabel tm i (NullaryOp (ConstructLiteralValue tys vals)) = labelToDoc i "ConstructLiteralValue" 
    (bracketList renderColumnTypes tys <> comma
    $$ renderData [d]) (lookupTags i tm)
opDotLabel tm i (NullaryOp (ConstructLiteralTable tys vals)) = labelToDoc i "ConstructLiteralValue" 
        (bracketList renderColumnTypes tys <> comma
        $$ renderData d) (lookupTags i tm)
opDotLabel tm i (NullaryOp (TableRef n tys ks)) = labelToDoc i "TableRef"
        (quotes (text n) <> comma <+> bracketList renderScanColumn cols <> comma $$ renderTableKeys ks)
        (lookupTags i tm)
        
        
opDotLabel tm i (ProjectL info) = 
     labelToDoc i "Project" (bracketList renderProj info) (lookupTags i tm)
opDotLabel tm i (AggrL (ks, as)) = 
     labelToDoc i "Aggr" ((bracketList renderColID ks) <> comma <+> (bracketList renderAggregation as)) (lookupTags i tm)
opDotLabel tm i (OrdAggrL (ks, as)) = 
     labelToDoc i "OrdAggr" ((bracketList renderColID ks) <> comma <+> (bracketList renderAggregation as)) (lookupTags i tm)
opDotLabel tm i (UnionL) =
     labelToDoc i "Union" empty (lookupTags i tm)
opDotLabel tm i (InlineLoadL (c, d)) =
    labelToDoc i "InlineLoad"
    (bracketList renderColumnName c <> comma
     $$ renderData d <> comma
     $$ quotes comma <> comma
     <+> quotes semi <> comma
     <+> quotes (text "\"") <> comma
     <+> quotes (text "\\"))
    (lookupTags i tm)
opDotLabel tm i (SelectL info) =
     labelToDoc i "Select" (renderExpr info) (lookupTags i tm)
opDotLabel tm i (MergeUnionL info) =
     labelToDoc i "MergeUnion" (renderJoinArgs info) (lookupTags i tm)
opDotLabel tm i (MergeDiffL info) =
     labelToDoc i "MergeDiff" (renderJoinArgs info) (lookupTags i tm)
opDotLabel tm i (MergeJoin1L info) =
     labelToDoc i "MergeJoin1" (renderJoinArgs info) (lookupTags i tm)
opDotLabel tm i (MergeJoinNL info) =
     labelToDoc i "MergeJoinN" (renderJoinArgs info) (lookupTags i tm)
opDotLabel tm i (HashJoin01L info) = 
     labelToDoc i "HashJoin01" (renderJoinArgs info) (lookupTags i tm)
opDotLabel tm i (HashJoin1L info) = 
     labelToDoc i "HashJoin1" (renderJoinArgs info) (lookupTags i tm)
opDotLabel tm i (HashJoinNL info) = 
     labelToDoc i "HashJoinN" (renderJoinArgs info) (lookupTags i tm)
opDotLabel tm i (StableSortL info) = 
     labelToDoc i "StableSort" (bracketList renderSortCol info) (lookupTags i tm)
opDotLabel tm i (SortL info) = 
     labelToDoc i "Sort" (bracketList renderSortCol info) (lookupTags i tm)
opDotLabel tm i (CartProdL (Just card)) = 
     labelToDoc i "Cartprod" (int card) (lookupTags i tm)
opDotLabel tm i (CartProdL Nothing) = 
     labelToDoc i "Cartprod" empty (lookupTags i tm)
opDotLabel tm i (FlowMatL) =  labelToDoc i "FlowMat" empty (lookupTags i tm)
opDotLabel tm i (MScanL (t, cols, keys)) =
     labelToDoc i "MScan" (renderTableName t <> comma <+> bracketList renderScanColumn cols <> comma $$ renderTableKeys keys) (lookupTags i tm)
opDotLabel tm i (AppendL info) =
     labelToDoc i "Append" (renderTableName info) (lookupTags i tm)
opDotLabel tm i NullOpL =
     labelToDoc i "NullOp" empty (lookupTags i tm) 
opDotLabel tm i (ReuseL label) =
     labelToDoc i "Reuse" (text label) (lookupTags i tm)
{-
simpleProj :: Proj -> Bool
simpleProj (ExprProj _ (Column _)) = True
simpleProj (ExprProj _ _) = False
simpleProj (ColProj _) = True

opDotColor :: X100Label -> DotColor
opDotColor (ProjectL ps) = 
  if all simpleProj ps
  then Gray
  else LightSkyBlue
opDotColor (AggrL _) = Tomato
opDotColor (OrdAggrL _) = Salmon
opDotColor (UnionL) = Gray
opDotColor (InlineLoadL _) = DimGray
opDotColor (SelectL _) = Gold
opDotColor (MergeUnionL _) = Tan
opDotColor (MergeJoin1L _) = Tan
opDotColor (MergeJoinNL _) = Tan
opDotColor (MergeDiffL _) = Tan
opDotColor (StableSortL _) = Red
opDotColor (SortL _) = Red
opDotColor (CartProdL _) = Crimson
opDotColor (HashJoin01L _) = Green
opDotColor (HashJoin1L _) = Green
opDotColor (HashJoinNL _) = Green
opDotColor (FlowMatL) = DimGray
opDotColor (MScanL _) = Gray
opDotColor (AppendL _) = Sienna
opDotColor NullOpL = Beige
opDotColor (ReuseL _) = DodgerBlue
-}
-- Dot colors
data DotColor = Tomato
              | Salmon
              | Gray
              | DimGray
              | Gold
              | Tan
              | Red
              | Crimson
              | Green
              | Sienna
              | Beige
              | DodgerBlue
              | LightSkyBlue

renderColor :: DotColor -> Doc
renderColor Tomato = text "tomato"
renderColor Salmon = text "salmon"
renderColor Gray = text "gray"
renderColor DimGray = text "dimgray"
renderColor Gold = text "gold"
renderColor Tan = text "tan"
renderColor Red = text "red"
renderColor Crimson = text "crimson"
renderColor Green = text "green"
renderColor Sienna = text "sienna"
renderColor Beige = text "beige"
renderColor DodgerBlue = text "dodgerblue"
renderColor LightSkyBlue = text "lightskyblue"
{-
escapeLabel :: String -> String
escapeLabel s = concatMap escapeChar s

escapeChar :: Char -> [Char]
escapeChar '\n' = ['\\', 'n']
escapeChar '\\' = ['\\', '\\']
escapeChar '\"' = ['\\', '"']
escapeChar c = [c]
-}
-- Type of Dot style options
data DotStyle = Solid

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
preamble = graphAttributes $$ nodeAttributes
    where nodeAttributes = text "node" <+> (brackets $ text "style=filled" <> comma <+> text "shape=box") <> semi
          graphAttributes = text "ordering=out;"

renderDotNode :: DotNode -> Doc
renderDotNode (DotNode n l c s) =
    int n 
    <+> (brackets $ (((text "label=") <> (doubleQuotes $ text l))
                     <> comma
                     <+> (text "color=") <> (renderColor c)
                     <> styleDoc))
    <> semi
    where styleDoc = 
              case s of
                  Just Solid -> comma <+> text "solid"
                  Nothing -> empty

renderDotEdge :: DotEdge -> Doc
renderDotEdge (DotEdge u v) = int u <+> text "->" <+> int v <> semi

-- | Render a Dot document from the preamble, nodes and edges
renderDot :: [DotNode] -> [DotEdge] -> Doc
renderDot ns es = text "digraph" <> (braces $ preamble $$ nodeSection $$ edgeSection)
    where nodeSection = vcat $ map renderDotNode ns 
          edgeSection = vcat $ map renderDotEdge es

-- | Create an abstract Dot node from an X100 operator description
constructDotNode :: [AlgNode] -> NodeMap [Tag] -> (AlgNode, VL) -> DotNode
constructDotNode rootNodes ts (n, op) = 
    if elem n rootNodes then
        DotNode n l c (Just Solid)
    else
        DotNode n l c Nothing
    where l = escapeLabel $ render $ opDotLabel ts n op
          c = opDotColor op

-- | Create an abstract Dot edge
constructDotEdge :: (AlgNode, AlgNode) -> DotEdge 
constructDotEdge = uncurry DotEdge

-- | extract the operator descriptions and list of edges from a DAG
extractGraphStructure :: Dag.Operator a => Dag.AlgebraDag a 
                     -> ([(AlgNode, VL)], [(AlgNode, AlgNode)])
extractGraphStructure toLabel d = (labels, childs)
    where nodes = Dag.topsort d
          operators = zip nodes $ map (flip Dag.operator d) nodes
          labels = map (\(n, op) -> (n, toLabel op)) operators
          childs = concat $ map (\(n, op) -> zip (repeat n) (Dag.opChildren op)) operators

-- | Render an VL plan into a dot file (GraphViz).
renderVLDot :: NodeMap [Tag] -> [AlgNode] -> NodeMap VL -> String
renderVLDot ts roots m = render $ renderDot dotNodes dotEdges
    where (opLabels, edges) = extractGraphStructure dPruned
          d = Dag.mkDag m roots
          dPruned = case Dag.pruneUnused d of
                      Just d' -> d'
                      Nothing  -> d
          dotNodes = map (constructDotNode roots ts) opLabels
          dotEdges = map constructDotEdge edges

{-
tagOfLink :: X100ReuseAlgebra -> Maybe [Tag]
tagOfLink (BinOp _ (Label ll) (Label lr)) = Just ["Label: Left = " ++ ll ++ "Right = " ++ lr]
tagOfLink (BinOp _ (Label l) _)           = Just ["Label: Left = " ++ l]
tagOfLink (BinOp _ _ (Label l))           = Just ["Label: Right = " ++ l]
tagOfLink (UnOp _ (Label l))              = Just ["Label: " ++ l]
tagOfLink _                               = Nothing

addLinkLabels :: NodeMap [Tag] -> NodeMap X100ReuseAlgebra -> NodeMap [Tag]
addLinkLabels ts ops = Map.unionWith (++) ts $ Map.foldrWithKey (\n o m -> case tagOfLink o of
                                                                    Just t -> Map.insert n t m
                                                                    Nothing -> m) Map.empty ops
-}