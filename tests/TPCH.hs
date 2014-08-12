{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ViewPatterns          #-}

module TPCH where

import Database.DSH

-- primary key: l_orderkey, l_linenumber
data LineItem = LineItem
    { l_comment       :: Text
    , l_commitdate    :: Integer
    , l_discount      :: Double
    , l_extendedprice :: Double
    , l_linenumber    :: Integer
    , l_linestatus    :: Text
    , l_orderkey      :: Integer
    , l_partkey       :: Integer
    , l_quantity      :: Double
    , l_receiptdate   :: Integer
    , l_returnflag    :: Text
    , l_shipdate      :: Integer
    , l_shipinstruct  :: Text
    , l_shipmode      :: Text
    , l_suppkey       :: Integer
    , l_tax           :: Double
    }

deriveDSH ''LineItem
deriveTA ''LineItem
generateTableSelectors ''LineItem

data Supplier = Supplier
    { s_acctbal   :: Double -- should be decimal
    , s_address   :: Text
    , s_comment   :: Text
    , s_name      :: Text
    , s_nationkey :: Integer
    , s_phone     :: Text
    , s_suppkey   :: Integer
    }

deriveDSH ''Supplier
deriveTA ''Supplier
generateTableSelectors ''Supplier

data Part = Part
    { p_brand       :: Text
    , p_comment     :: Text
    , p_container   :: Text
    , p_mfgr        :: Text
    , p_name        :: Text
    , p_partkey     :: Integer
    , p_retailprice :: Double -- should be decimal
    , p_size        :: Integer
    , p_type        :: Text
    }

deriveDSH ''Part
deriveTA ''Part
generateTableSelectors ''Part

data PartSupp = PartSupp
    { ps_availqty   :: Integer
    , ps_comment    :: Text
    , ps_partkey    :: Integer
    , ps_suppkey    :: Integer
    , ps_supplycost :: Double -- should be decimal
    }

deriveDSH ''PartSupp
deriveTA ''PartSupp
generateTableSelectors ''PartSupp

data Nation = Nation
    { n_comment   :: Text
    , n_name      :: Text
    , n_nationkey :: Integer
    , n_regionkey :: Integer
    }

deriveDSH ''Nation
deriveTA ''Nation
generateTableSelectors ''Nation

data Region = Region
    { r_comment   :: Text
    , r_name      :: Text
    , r_regionkey :: Integer
    }

deriveDSH ''Region
deriveTA ''Region
generateTableSelectors ''Region

data Order = Order
    { o_clerk         :: Text
    , o_comment       :: Text
    , o_custkey       :: Integer
    , o_orderdate     :: Integer
    , o_orderkey      :: Integer
    , o_orderpriority :: Text
    , o_orderstatus   :: Text
    , o_shippriority  :: Integer
    , o_totalprice    :: Double
    }

deriveDSH ''Order
deriveTA ''Order
generateTableSelectors ''Order

data Customer = Customer
    { c_acctbal    :: Double
    , c_address    :: Text
    , c_comment    :: Text
    , c_custkey    :: Integer
    , c_mktsegment :: Text
    , c_name       :: Text
    , c_nationkey  :: Integer
    , c_phone      :: Text
    }

deriveDSH ''Customer
deriveTA ''Customer
generateTableSelectors ''Customer

parts :: Q [Part]
parts = table "part" $ TableHints [ Key ["p_partkey"] ] NonEmpty

suppliers :: Q [Supplier]
suppliers = table "supplier" $ TableHints [ Key ["s_suppkey"] ] NonEmpty

partsupps :: Q [PartSupp]
partsupps = table "partsupp" $ TableHints [Key ["ps_partkey", "ps_suppkey"]] NonEmpty

nations :: Q [Nation]
nations = table "nation" $ TableHints [Key ["n_nationkey"]] NonEmpty

regions :: Q [Region]
regions = table "region" $ TableHints [Key ["r_regionkey"]] NonEmpty

orders :: Q [Order]
orders = table "orders" $ TableHints [Key ["o_orderkey"]] NonEmpty

lineitems :: Q [LineItem]
lineitems = table "lineitem" $ TableHints [Key ["l_orderkey", "l_linenumber"]] NonEmpty

customers :: Q [Customer]
customers = table "customer" $ TableHints [Key ["c_custkey"]] NonEmpty



