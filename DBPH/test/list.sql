NestedVector 
SELECT a0000.iter1_nat
   FROM (VALUES (1, 1, 1),
               (1, 2, 1),
               (1, 2, 2)) AS a0000(iter1_nat,
        item5_nat,
        pos6_nat)
  ORDER BY a0000.iter1_nat ASC, a0000.item5_nat ASC, a0000.pos6_nat ASC;
 (ValueVector 
WITH
-- binding due to rownum operator
t0000 (item6_nat, pos7_nat, item8_nat) AS
  (SELECT a0000.item6_nat, a0000.pos7_nat,
          ROW_NUMBER () OVER (ORDER BY a0000.item6_nat ASC, a0000.pos7_nat ASC)
          AS item8_nat
     FROM (VALUES (1, 1),
                 (2, 1),
                 (2, 2)) AS a0000(item6_nat,
          pos7_nat))

SELECT (a0002.item1_int + a0002.item4_int) AS item12_int,
        a0001.item8_nat AS pos9_nat
   FROM t0000 AS a0001,
        (VALUES (1, 1, 1, 1),
               (2, 2, 1, 1),
               (3, 2, 2, 1)) AS a0002(item1_int,
        item2_nat,
        pos3_nat,
        item4_int)
  ORDER BY a0001.item8_nat ASC, a0001.item8_nat ASC, a0002.item2_nat ASC,
        a0002.pos3_nat ASC;
)