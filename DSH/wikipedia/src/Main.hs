module Main where

import Data.List

import Data.Map (Map,(!))
import qualified Data.Map as Map

import qualified Data.Set as Set

import Control.Exception

import qualified Data.IGraph as Graph

import Database.DSH (Q,QA,toQ,disconnect,csvExport)
import Database.DSH.Compiler (fromQ,debugSQL)

import Records
import Wikipedia

runQ :: (QA a) => Q a -> IO a
runQ q =
  bracket getConnection
          disconnect
          (\conn -> fromQ conn q)

debugQ :: (QA a) => Q a -> IO ()
debugQ q =
  bracket getConnection
          disconnect
          (\conn -> (debugSQL conn q) >>= putStrLn)

resolveRedirects :: [(Integer,Integer)] -> Map Integer (Maybe RevisionStat) -> [(Integer,Integer)]
resolveRedirects eds revStatsMap = concatMap func eds
  where
  edsMap       = Map.fromList eds
  func (fr,to) = case Map.lookup to revStatsMap of
                   Nothing                                        -> [(fr,to)]
                   Just Nothing                                   -> [(fr,to)]
                   Just (Just rs) | rev_stat_is_redirect rs == 0  -> [(fr,to)]
                   Just (Just  _) | otherwise                     ->
                     case Map.lookup to edsMap of
                       Nothing  -> []
                       Just to' -> [(fr,to')]

writeHeader :: IO ()
writeHeader = writeFile "header.csv" (concat content ++ "\n")
  where
  content = intersperse "," [ "day"
                            , "page_id"
                            , "indegree_centrality"
                            , "eco_indegree_centrality"
                            , "soc_indegree_centrality"
                            , "outward_links"
                            , "click_number"
                            , "revision_number"
                            , "author_number"
                            , "page_lengths"
                            , "rev_stat_image_link_number"
                            , "rev_stat_is_explanation"
                            , "rev_stat_is_redirect"
                            , "rev_stat_literature_number"
                            , "rev_stat_reference_number"
                            , "rev_stat_external_links"
                            , "global_node_number"
                            , "global_closeness_in_centrality"
                            , "global_eigenvector_centrality"
                            , "eco_node_number"
                            , "soc_node_number"
                            , "eco_betweenness_centrality"
                            , "soc_betweenness_centrality"
                            , "eco_closeness_in_centrality"
                            , "soc_closeness_in_centrality"
                            , "eco_closeness_out_centrality"
                            , "soc_closeness_out_centrality"
                            ]


runDay :: Double -> IO ()
runDay day = do
  rEcoPageIds              <- fmap Set.fromList (runQ relevantEcoPageIds)
  rSocPageIds              <- fmap Set.fromList (runQ relevantSocPageIds)
  rNoRevisions             <- fmap Map.fromList (runQ (forRelevantPages (toQ day) noRevision))
  rNoLinks                 <- fmap Map.fromList (runQ (forRelevantPages (toQ day) noLink))
  rCentralities            <- fmap Map.fromList (runQ (forRelevantPages (toQ day) (centrality relevantLinks)))
  rEcoCentralities         <- fmap Map.fromList (runQ (forRelevantPages (toQ day) (centrality relevantEcoLinks)))
  rSocCentralities         <- fmap Map.fromList (runQ (forRelevantPages (toQ day) (centrality relevantSocLinks)))
  rOutwardLinkNumbers      <- fmap Map.fromList (runQ (forRelevantPages (toQ day) outwardLinkNumber))
  rClickNumbers            <- fmap Map.fromList (runQ (forRelevantPages (toQ day) clickNumber))
  rRevisionNumbers         <- fmap Map.fromList (runQ (forRelevantPages (toQ day) revisionNumber))
  rAuthorNumbers           <- fmap Map.fromList (runQ (forRelevantPages (toQ day) authorNumber))
  rPageLengths             <- fmap Map.fromList (runQ (forRelevantPages (toQ day) pageLength))
  rLatestRevisionStats     <- fmap Map.fromList (runQ (forRelevantPages (toQ day) latestRevisionStat))
  rGlobalNodeNumber        <- fmap Map.fromList (runQ (forRelevantPages (toQ day) globalNodeNumber))
  rGlobalClosenessIn       <- fmap Map.fromList (runQ (forRelevantPages (toQ day) globalClosenessIn))
  rGlobalEigenvector       <- fmap Map.fromList (runQ (forRelevantPages (toQ day) globalEigenvector))
  rEcoNetwork              <- runQ (ecoNetwork (toQ day))
  rSocNetwork              <- runQ (socNetwork (toQ day))

  let rEcoGraph       = Graph.make (resolveRedirects rEcoNetwork rLatestRevisionStats)
  let rSocGraph       = Graph.make (resolveRedirects rSocNetwork rLatestRevisionStats)
  let rEcoBetweenness = Map.fromList (Graph.betweenness rEcoGraph)
  let rSocBetweenness = Map.fromList (Graph.betweenness rSocGraph)
  let ecoNodeNumber   = fromIntegral $ length $ nub $ concatMap (\(fr,to) -> [fr,to]) rEcoNetwork
  let socNodeNumber   = fromIntegral $ length $ nub $ concatMap (\(fr,to) -> [fr,to]) rSocNetwork

  let na  = (-99)
  let nad = (-99.0)

  let result =  [ let revStat = (rLatestRevisionStats ! pid)
                  in  if (rNoRevisions ! pid && rNoLinks ! pid)
                        then (day,pid,na,na,na,na,na,na,na,na,na,na,na,na,na,na,na,nad,nad,na,na,nad,nad,nad,nad,nad,nad)
                        else ( day
                             , pid
                             , rCentralities       ! pid
                             , if pid `Set.member` rEcoPageIds then rEcoCentralities ! pid else na
                             , if pid `Set.member` rSocPageIds then rSocCentralities ! pid else na
                             , rOutwardLinkNumbers ! pid
                             , rClickNumbers       ! pid
                             , rRevisionNumbers    ! pid
                             , rAuthorNumbers      ! pid
                             , maybe 0 id (rPageLengths ! pid)
                             , maybe 0 (rev_stat_image_link_number) revStat
                             , maybe 0 (rev_stat_is_explanation   ) revStat
                             , maybe 0 (rev_stat_is_redirect      ) revStat
                             , maybe 0 (rev_stat_literature_number) revStat
                             , maybe 0 (rev_stat_reference_number ) revStat
                             , maybe 0 (rev_stat_external_links   ) revStat
                             , rGlobalNodeNumber   ! pid
                             , rGlobalClosenessIn  ! pid
                             , rGlobalEigenvector  ! pid
                             , ecoNodeNumber
                             , socNodeNumber
                             , if (Graph.member rEcoGraph pid) then rEcoBetweenness ! pid else nad
                             , if (Graph.member rSocGraph pid) then rSocBetweenness ! pid else nad
                             , if (Graph.member rEcoGraph pid) then Graph.closenessIn  rEcoGraph pid else nad
                             , if (Graph.member rSocGraph pid) then Graph.closenessIn  rSocGraph pid else nad
                             , if (Graph.member rEcoGraph pid) then Graph.closenessOut rEcoGraph pid else nad
                             , if (Graph.member rSocGraph pid) then Graph.closenessOut rSocGraph pid else nad
                             )
                | pid <- Map.keys rLatestRevisionStats
                ]

  csvExport ("eco_soc_mul_" ++ show day ++ ".csv") result

-- writeInvHeader :: IO ()
-- writeInvHeader = writeFile "time_invariant_header.csv" (concat content ++ "\n")
--   where
--   content = intersperse "," [ "page_id"
--                             , "page_title"
--                             , "page_super_category"
--                             , "page_first_revision_time"
--                             , "page_langlinks"
--                             , "page_renamed"
--                             ]
--
-- runInv :: IO ()
-- runInv = do
--   rPageTitles             <- fmap Map.fromList (runQ (forRelevantPagesInv pageTitle))
--   rSuperCategories        <- fmap Map.fromList (runQ (forRelevantPagesInv superCategory))
--   rPageFirstRevisionTime  <- fmap Map.fromList (runQ (forRelevantPagesInv pageFirstRevisionTime))
--   rPageLangLinks          <- fmap Map.fromList (runQ (forRelevantPagesInv pageLangLinks))
--   rPageRenameds           <- fmap Map.fromList (runQ (forRelevantPagesInv pageRenamed))
--   let result =  [ ( pid
--                   , rPageTitles             ! pid
--                   , rSuperCategories        ! pid
--                   , rPageFirstRevisionTime  ! pid
--                   , rPageLangLinks          ! pid
--                   , (fromIntegral (fromEnum (rPageRenameds ! pid))) :: Integer
--                   )
--                 | pid <- Map.keys rPageTitles
--                 ]
--   csvExport ("eco_soc_time_invariant.csv") result

-- Mondays from Mon, 10 Dec 2007 04:00:00 GMT
--         to   Mon, 08 Nov 2010 04:00:00 GMT
days :: [Double]
days = take 153 (iterate (+ 7 * 24 * 60 * 60) 1197259200)

main :: IO ()
main = do
  -- writeInvHeader
  -- runInv
  writeHeader
  mapM_ runDay days -- (take 1 days)