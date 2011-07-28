NestedVector 
SELECT a0000.iter1_nat
   FROM (VALUES (1, 1, 1),
               (1, 2, 1),
               (1, 2, 2)) AS a0000(iter1_nat,
        item5_nat,
        pos6_nat)
  ORDER BY a0000.iter1_nat ASC, a0000.item5_nat ASC, a0000.pos6_nat ASC;
 (NestedVector 
WITH
-- binding due to rownum operator
t0000 (item3_nat, pos4_nat, item5_nat) AS
  (SELECT a0000.item3_nat, a0000.pos4_nat,
          ROW_NUMBER () OVER (ORDER BY a0000.item3_nat ASC, a0000.pos4_nat ASC)
          AS item5_nat
     FROM (VALUES (1, 1),
                 (2, 1),
                 (2, 2)) AS a0000(item3_nat,
          pos4_nat))

SELECT a0001.item5_nat AS pos6_nat
   FROM t0000 AS a0001,
        (VALUES (1, 1),
               (2, 1),
               (2, 2)) AS a0002(item11_nat,
        pos12_nat)
  ORDER BY a0001.item5_nat ASC, a0001.item5_nat ASC, a0002.item11_nat ASC,
        a0002.pos12_nat ASC;
 (ValueVector 
SELECT DENSE_RANK () OVER
        (ORDER BY a0002.item25_nat ASC, a0002.pos26_nat ASC, a0001.item5_nat
         ASC, a0001.pos6_nat ASC) AS item22_nat,
        (a0000.item10_int + a0000.item13_int) AS item17_int
   FROM (VALUES (1, 1, 1, 1),
               (2, 2, 1, 1),
               (3, 2, 2, 1)) AS a0000(item10_int,
        item11_nat,
        pos12_nat,
        item13_int),
        (VALUES (1, 1),
               (2, 1),
               (2, 2)) AS a0001(item5_nat,
        pos6_nat),
        (VALUES (1, 1),
               (2, 1),
               (2, 2)) AS a0002(item25_nat,
        pos26_nat)
  ORDER BY a0002.item25_nat ASC, a0002.pos26_nat ASC, a0001.item5_nat ASC,
        a0001.pos6_nat ASC, a0002.item25_nat ASC, a0002.pos26_nat ASC,
        a0001.item5_nat ASC, a0001.pos6_nat ASC, a0000.item11_nat ASC,
        a0000.pos12_nat ASC;
))