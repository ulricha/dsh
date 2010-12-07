{-# LANGUAGE TransformListComp #-}
module PaperExampleHS where
    
import GHC.Exts (the)
import Data.List (nub)

type Facility = String
type Cat      = String
type Feature  = String
type Meaning  = String

facilities :: [(Facility, Cat)]
facilities = [ ("SQL", "QLA"),
               ("ODBC", "API"),
               ("LINQ", "LIN"),
               ("Links", "LIN"),
               ("Rails", "ORM"),
               ("Ferry", "LIB"),
               ("Kleisli", "QLA"),
               ("ADO.NET", "ORM"),
               ("HaskellDB", "LIB")]
               
features :: [(Facility, Feature)]
features = [("Kleisli","nest")
          ,("Kleisli","comp")
          ,("Kleisli","type")
          ,("Links","comp")
          ,("Links","type")
          ,("Links","SQL")
          ,("LINQ","nest")
          ,("LINQ","comp")
          ,("LINQ","type")
          ,("HaskellDB","comp")
          ,("HaskellDB","type")
          ,("HaskellDB","SQL")
          ,("SQL","aval")
          ,("SQL","type")
          ,("SQL","SQL")
          ,("Rails","nest")
          ,("Rails","maps")
          ,("ADO.NET","maps")
          ,("ADO.NET","comp")
          ,("ADO.NET","type")
          ,("Ferry","list")
          ,("Ferry","nest")
          ,("Ferry","comp")
          ,("Ferry","aval")
          ,("Ferry","type")
          ,("Ferry","SQL")] 
          
meanings :: [(Feature, Meaning)]
meanings = [("maps","admits user-defined object mappings"),
            ("list","respects list order"),
            ("nest","supports data nesting"),
            ("comp","has compositional syntax and semantics"),
            ("aval","avoids query avalanches"),
            ("type","is statically type-checked"),
            ("SQL","guarantees translation to SQL")]

hasFeatures :: String -> [String] 
hasFeatures f = [feat | (fac,feat) <- features, fac == f]

means :: String -> String
means f = head [mean | (feat,mean) <- meanings, feat == f ]

query :: [(String , [String ])] 
query = [(the cat, nub $ concat $ map (map means . hasFeatures) fac) 
        | (fac, cat) <- facilities, then group by cat]

main :: IO ()
main = print query
              