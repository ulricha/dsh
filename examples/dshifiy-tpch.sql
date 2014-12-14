alter table supplier alter column s_acctbal type real;

alter table lineitem alter column l_acctbal type real;

alter table customer alter column c_acctbal type real;

alter table lineitem alter column l_quantity type real;
alter table lineitem alter column l_extendedprice type real;
alter table lineitem alter column l_discount type real;
alter table lineitem alter column l_tax type real;

alter table orders alter column o_totalprice type real;
alter table orders alter column o_orderdate type int using extract(epoch from o_orderdate); 

alter table lineitem alter column l_shipdate type int using extract(epoch from l_shipdate); 
alter table lineitem alter column l_commitdate type int using extract(epoch from l_commitdate); 
alter table lineitem alter column l_receiptdate type int using extract(epoch from l_receiptdate); 

alter table part alter column p_retailprice type real;
