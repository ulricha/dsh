{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses, CPP #-}

module Records where

import Prelude ()
import Database.DSH

import Database.HDBC.PostgreSQL

#define getConnectionDef (connectPostgreSQL "user = 'giorgidz' host = 'localhost' dbname = 'giorgidz'")

getConnection :: IO Connection
getConnection = getConnectionDef

$(generateTableRecordInstances getConnectionDef "revisions"            "Revision"            [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "revision_stats"       "RevisionStat"        [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "pages"                "Page"                [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "links"                "Link"                [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "clicks"               "Click"               [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "category_pages"       "CategoryPage"        [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "super_category_pages" "SuperCategoryPage"   [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "langlinks"            "LangLink"            [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "user_groups"          "UserGroup"           [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "network_stats"        "NetworkStat"         [''Show,''Eq,''Ord])
-- $(generateTableRecordInstances getConnectionDef "renames2"             "Rename"              [''Show,''Eq,''Ord])



-- days :: Q [Double]
-- days = tableWithKeys "days" [["day"]]

revisions :: Q [Revision]
revisions = tableWithKeys "revisions" [["rev_id"]]

revision_stats :: Q [RevisionStat]
revision_stats = tableWithKeys "revision_stats" [["rev_stat_revision"]]

pages :: Q [Page]
pages = tableWithKeys "pages" [["page_id"]]

links :: Q [Link]
links = tableWithKeys "links" [["link_from_page", "link_to_page", "link_revision"]]

clicks :: Q [Click]
clicks = tableWithKeys "clicks" [["click_date", "click_page_id"]]

category_pages :: Q [CategoryPage]
category_pages = tableWithKeys "categorie_pages" [["cat_title", "cat_page"]]

super_category_pages :: Q [SuperCategoryPage]
super_category_pages = tableWithKeys "super_category_pages" [["scp_page"]]

langlinks :: Q [LangLink]
langlinks = tableWithKeys "langlinks" [["ll_page","ll_lang"]]

user_groups :: Q [UserGroup]
user_groups = tableWithKeys "user_groups" [["ug_user"]]

network_stats :: Q [NetworkStat]
network_stats = tableWithKeys "network_stats" [["network_stat_date","network_stat_page"]]

-- renames :: Q [Integer]
-- renames = table "renames2"