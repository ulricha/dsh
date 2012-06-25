{-# LANGUAGE MonadComprehensions, RebindableSyntax, OverloadedStrings, ViewPatterns #-}

module Wikipedia where

import Prelude ()
import Database.DSH
import Records

pageTitle :: Q Integer -> Q Text
pageTitle pageId =
    head
  $ map page_titleQ
  $ filter (\p -> page_idQ p == pageId)
  $ pages

superCategory :: Q Integer -> Q Text
superCategory pageId =
    head
  $ map scp_nameQ
  $ filter (\scp -> scp_pageQ scp == pageId)
  $ super_category_pages

pageFirstRevisionTime :: Q Integer -> Q Double
pageFirstRevisionTime pageId =
    minimum
  $ map rev_timeQ
  $ filter (\r -> rev_pageQ r == pageId)
  $ revisions

pageFirstRevision :: Q Integer -> Q Integer
pageFirstRevision pageId =
    minimum
  $ map rev_idQ
  $ filter (\r -> rev_pageQ r == pageId)
  $ revisions

relevantPageIds :: Q [Integer]
relevantPageIds = map scp_pageQ super_category_pages

relevantEcoPageIds :: Q [Integer]
relevantEcoPageIds =
    map scp_pageQ
  $ filter (\scp -> scp_nameQ scp == "eco" || scp_nameQ scp == "mul")
  $ super_category_pages

relevantSocPageIds :: Q [Integer]
relevantSocPageIds =
    map scp_pageQ
  $ filter (\scp -> scp_nameQ scp == "soc" || scp_nameQ scp == "mul")
  $ super_category_pages

userBots :: Q [Integer]
userBots =
    map ug_userQ
  $ filter (\ug -> ug_groupQ ug == "bot")
  $ user_groups

relevantLinks :: Q Double -> Q [Link]
relevantLinks day =
    nub
  $ filter (\l -> link_to_pageQ l `elem` relevantPageIds)
  $ filter (\l -> link_addedQ l < day && link_removedQ l > day)
  $ links

relevantEcoLinks :: Q Double -> Q [Link]
relevantEcoLinks day =
    nub
  $ filter (\l -> link_to_pageQ l   `elem` relevantEcoPageIds)
  $ filter (\l -> link_from_pageQ l `elem` relevantEcoPageIds)
  $ filter (\l -> link_addedQ l < day && link_removedQ l > day)
  $ links

relevantSocLinks :: Q Double -> Q [Link]
relevantSocLinks day =
    nub
  $ filter (\l -> link_to_pageQ l   `elem` relevantSocPageIds)
  $ filter (\l -> link_from_pageQ l `elem` relevantSocPageIds)
  $ filter (\l -> link_addedQ l < day && link_removedQ l > day)
  $ links

centrality :: (Q Double -> Q [Link]) -> Q Double -> Q Integer -> Q Integer
centrality pageLinks day pageId =
    length
  $ filter (\l -> link_to_pageQ l == pageId)
  $ pageLinks day

ecoNetwork :: Q Double -> Q [(Integer,Integer)]
ecoNetwork day =
    map (\l -> tuple (link_from_pageQ l, link_to_pageQ l))
  $ relevantEcoLinks day

socNetwork :: Q Double -> Q [(Integer,Integer)]
socNetwork day =
    map (\l -> tuple (link_from_pageQ l, link_to_pageQ l))
  $ relevantSocLinks day

revTime :: Q Integer -> Q Double
revTime revId = head
  [ rev_timeQ rev
  | rev <- revisions
  , rev_idQ rev == revId
  ]

clickNumber :: Q Double -> Q Integer -> Q Integer
clickNumber day pageId =
    sum
  $ map click_numberQ
  $ filter (\c -> day - 36000 < click_dateQ c && click_dateQ c < day && click_page_idQ c == pageId)
  $ clicks

revisionNumber :: Q Double -> Q Integer -> Q Integer
revisionNumber day pageId =
    length
  $ filter (\r -> rev_userQ r `notElem` userBots)
  $ filter (\r -> rev_timeQ r < day && rev_pageQ r == pageId)
  $ revisions

authorNumber :: Q Double -> Q Integer -> Q Integer
authorNumber day pageId =
    length
  $ nub
  $ map rev_userQ
  $ filter (\r -> rev_userQ r `notElem` userBots)
  $ filter (\r -> rev_timeQ r < day &&  rev_pageQ r == pageId)
  $ revisions

pageLength :: Q Double -> Q Integer -> Q (Maybe Integer)
pageLength day pageId =
    listToMaybe
  $ map    rev_lenQ
  $ filter (\r -> rev_timeQ r <  day)
  $ filter (\r -> rev_pageQ r == pageId)
  $ reverse
  $ sortWith rev_timeQ
  $ revisions

noRevision :: Q Double -> Q Integer -> Q Bool
noRevision day pageId = null
  [ toQ () | rev <- revisions
  , rev_pageQ rev == pageId
  , rev_timeQ rev <  day
  ]

noLink :: Q Double -> Q Integer -> Q Bool
noLink day pageId = null
  [ toQ () | link <- links
  , link_to_pageQ link == pageId
  , link_addedQ link <  day
  ]

pageLangLinks :: Q Integer -> Q Integer
pageLangLinks pageId = length
  [ pageId
  | ll <- langlinks
  , ll_pageQ ll == pageId
  ]

-- pageRenamed :: Q Integer -> Q Bool
-- pageRenamed pageId = pageId `elem` (renames)

latestRevisionStat :: Q Double -> Q Integer -> Q (Maybe RevisionStat)
latestRevisionStat day pageId =
    listToMaybe
  $ filter (\rs -> revTime (rev_stat_revisionQ rs) < day)
  $ filter (\rs -> rev_stat_pageQ rs == pageId)
  $ reverse
  $ sortWith rev_stat_revisionQ
  $ revision_stats

globalNodeNumber :: Q Double -> Q Integer -> Q Integer
globalNodeNumber date page =
    head
  $ map network_stat_nodesQ
  $ filter (\ns -> network_stat_pageQ ns == page)
  $ filter (\ns -> network_stat_dateQ ns == date)
  $ network_stats

globalClosenessIn :: Q Double -> Q Integer -> Q Double
globalClosenessIn date page =
    head
  $ map network_stat_closeness_inQ
  $ filter (\ns -> network_stat_pageQ ns == page)
  $ filter (\ns -> network_stat_dateQ ns == date)
  $ network_stats

globalEigenvector :: Q Double -> Q Integer -> Q Double
globalEigenvector date page =
    head
  $ map network_stat_eigenvectorQ
  $ filter (\ns -> network_stat_pageQ ns == page)
  $ filter (\ns -> network_stat_dateQ ns == date)
  $ network_stats

outwardLinkNumber :: Q Double -> Q Integer -> Q Integer
outwardLinkNumber day pageId = length
  [ pageId
  | link <- links
  , link_from_pageQ link == pageId
  , link_addedQ   link < day
  , link_removedQ link > day
  ]

forRelevantPages :: (QA a) => Q Double -> (Q Double -> Q Integer -> Q a) -> Q [(Integer,a)]
forRelevantPages day f =
    map (\scp -> tuple (scp_pageQ scp, f day (scp_pageQ scp)))
  $ super_category_pages

forRelevantPagesInv :: (QA a) => (Q Integer -> Q a) -> Q [(Integer,a)]
forRelevantPagesInv f =
    map (\scp -> tuple (scp_pageQ scp, f (scp_pageQ scp)))
  $ super_category_pages