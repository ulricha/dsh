ValueVector 
WITH
-- binding due to rank operator
t0000 (item1_int, iter2_nat, item7_nat, pos8_nat, item5_nat) AS
  (SELECT a0000.item1_int, a0000.iter2_nat, a0000.item7_nat, a0000.pos8_nat,
          DENSE_RANK () OVER (ORDER BY a0000.item7_nat ASC, a0000.pos8_nat ASC)
          AS item5_nat
     FROM (VALUES (1, 1, 1, 1),
                 (2, 1, 2, 1),
                 (3, 1, 2, 2)) AS a0000(item1_int,
          iter2_nat,
          item7_nat,
          pos8_nat)),

-- binding due to duplicate elimination
t0001 (item1_int, iter2_nat, item5_nat) AS
  (SELECT DISTINCT a0001.item1_int, a0001.iter2_nat, a0001.item5_nat
     FROM t0000 AS a0001)

SELECT a0002.iter2_nat, a0002.item1_int
   FROM t0001 AS a0002
  ORDER BY a0002.iter2_nat ASC, a0002.item5_nat ASC;
