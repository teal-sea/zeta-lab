import FourPoint.Cells

/-! Chunk module 8 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_4 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (131/128:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (63/32:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
    rcases le_total x (1:ℝ) with hq00 | hq00
    · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
    exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
  have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
  have hw3 : (269743281/5000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
  linarith

set_option maxHeartbeats 20000000 in
lemma ch_86 (x y z : ℝ) (hx1 : (4277/4096:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (8119/4096:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (4287/4096:ℝ) with hc | hc
  · rcases le_total x (8559/8192:ℝ) with hc | hc
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17113/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17113/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17113/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17113/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17123/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17123/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17123/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17123/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total x (8559/8192:ℝ) with hc | hc
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17113/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17113/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17113/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17113/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17123/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17123/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17123/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17123/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_96 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (8119/4096:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (2141/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (4277/4096:ℝ) with hc | hc
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
          have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
          have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
          have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
          have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
          have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
            have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
            have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
            have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
            have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_97 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (8119/4096:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (2141/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (4277/4096:ℝ) with hc | hc
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
            have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
            have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_140 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (4297/4096:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (8109/4096:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (4287/4096:ℝ) with hc | hc
  · rcases le_total x (8589/8192:ℝ) with hc | hc
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (4172491/2000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (8589/8192:ℝ) with hc | hc
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (11686831/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (13013467/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_148 (x y z : ℝ) (hx1 : (2151/2048:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (4057/2048:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (2141/2048:ℝ) with hc | hc
  · rcases le_total x (4307/4096:ℝ) with hc | hc
    · rcases le_total y (8109/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
              have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (8109/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
              have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
            have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1001 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
            have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (4307/4096:ℝ) with hc | hc
    · rcases le_total y (8109/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (8109/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_153 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (2151/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4297/4096:ℝ) with hc | hc
  · rcases le_total y (8119/4096:ℝ) with hc | hc
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32461/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                  have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                  have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                  have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                  have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32461/16384:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                  have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                  have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                  have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                  have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32461/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                  have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                  have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                  have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                  have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32461/16384:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                  have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                  have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                  have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32471/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                  have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                  have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                  have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                  have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32471/16384:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                  have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                  have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32471/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                  have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                  have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                  have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · rcases le_total y (32461/16384:ℝ) with hc | hc
                · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                  have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                  have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                  have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                  have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32461/16384:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                  have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                  have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · rcases le_total y (32471/16384:ℝ) with hc | hc
                · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                  have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                  have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                  have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                  have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32481/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                  have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                  have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32481/16384:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                  have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                  have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                  have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                  have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32491/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                  have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                  have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                  have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                  have hw5 : (332952481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1096 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (8119/4096:ℝ) with hc | hc
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17193/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17193/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17193/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
            have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
            have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
            have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17193/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
            have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
            have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
            have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
            have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_162 (x y z : ℝ) (hx1 : (539/512:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1083/1024:ℝ) with hc | hc
  · rcases le_total y (2021/1024:ℝ) with hc | hc
    · rcases le_total z (1073/1024:ℝ) with hc | hc
      · rcases le_total x (2161/2048:ℝ) with hc | hc
        · rcases le_total y (4037/2048:ℝ) with hc | hc
          · rcases le_total z (2141/2048:ℝ) with hc | hc
            · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8069/4096:ℝ) with hc | hc
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (1679250671/2500000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                  have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (3220913463/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                  have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_375 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                have hw5 : (1157601093/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_911 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (2141/2048:ℝ) with hc | hc
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8079/4096:ℝ) with hc | hc
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                  have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                  have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_404 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                have hw5 : (1157601093/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_911 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8079/4096:ℝ) with hc | hc
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (4287/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8079/4096:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                  have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total y (4037/2048:ℝ) with hc | hc
          · rcases le_total z (2141/2048:ℝ) with hc | hc
            · have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
              have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
              have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2141/2048:ℝ) with hc | hc
            · have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
              have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
              have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
              have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (2161/2048:ℝ) with hc | hc
        · rcases le_total y (4037/2048:ℝ) with hc | hc
          · rcases le_total z (2151/2048:ℝ) with hc | hc
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
                have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_925 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_375 (x + y) (by linarith) (by linarith)
                have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_948 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
              have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2151/2048:ℝ) with hc | hc
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8079/4096:ℝ) with hc | hc
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
                  have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8079/4096:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                  have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
                  have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8079/4096:ℝ) with hc | hc
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
                  have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_375 (y + z) (by linarith) (by linarith)
                  have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_404 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1046 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (4037/2048:ℝ) with hc | hc
          · have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
            have hw5 : (262917659/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_970 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (2151/2048:ℝ) with hc | hc
            · have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
              have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1014 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
              have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
              have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1068 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (1073/1024:ℝ) with hc | hc
      · rcases le_total x (2161/2048:ℝ) with hc | hc
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · rcases le_total z (2141/2048:ℝ) with hc | hc
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · rcases le_total z (4277/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                    have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4277/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · rcases le_total z (4287/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                    have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4287/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                    have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                    have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
                  have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (2141/2048:ℝ) with hc | hc
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · rcases le_total z (4277/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                    have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                    have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                    have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4277/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                    have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                    have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                    have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                    have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (4277/4096:ℝ) with hc | hc
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                    have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                    have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                    have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                    have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · rcases le_total z (4287/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                    have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                    have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                    have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                    have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4287/4096:ℝ) with hc | hc
                  · rcases le_total x (8629/8192:ℝ) with hc | hc
                    · have hw0 : (60086101/5000000000000:ℝ) ≤ wfun x := wc_91 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                      have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                      have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
                      have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                      have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_94 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                      have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                      have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
                      have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                      have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (8629/8192:ℝ) with hc | hc
                    · have hw0 : (60086101/5000000000000:ℝ) ≤ wfun x := wc_91 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                      have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
                      have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                      have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_94 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                      have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
                      have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                      have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · rcases le_total z (4287/4096:ℝ) with hc | hc
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                    have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                    have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                    have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                    have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4287/4096:ℝ) with hc | hc
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                    have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                    have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                    have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                    have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                    linarith
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · rcases le_total z (2141/2048:ℝ) with hc | hc
            · have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
              have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (4327/4096:ℝ) with hc | hc
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (239941/400000000000:ℝ) ≤ wfun x := wc_96 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (239941/400000000000:ℝ) ≤ wfun x := wc_96 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
                  have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_466 (x + y) (by linarith) (by linarith)
                have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1046 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (2141/2048:ℝ) with hc | hc
            · rcases le_total x (4327/4096:ℝ) with hc | hc
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (239941/400000000000:ℝ) ≤ wfun x := wc_96 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                  have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (239941/400000000000:ℝ) ≤ wfun x := wc_96 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                  have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
                  have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_507 (x + y) (by linarith) (by linarith)
                have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1046 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (4327/4096:ℝ) with hc | hc
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (239941/400000000000:ℝ) ≤ wfun x := wc_96 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                  have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
                  have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (239941/400000000000:ℝ) ≤ wfun x := wc_96 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                  have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_375 (y + z) (by linarith) (by linarith)
                  have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1087 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_507 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1088 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (2161/2048:ℝ) with hc | hc
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · rcases le_total z (2151/2048:ℝ) with hc | hc
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · rcases le_total z (4297/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                    have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                    have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                    have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                    have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4297/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                    have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                    have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                    have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                    have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
                  have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_375 (y + z) (by linarith) (by linarith)
                  have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                  have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
                  have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                  have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1087 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_436 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1088 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (2151/2048:ℝ) with hc | hc
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · rcases le_total z (4297/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                    have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                    have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                    have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                    have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                    have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4297/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                    have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                    have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                    have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                    have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                    have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                    have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
                  have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1087 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                  have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                  have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1103 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (4317/4096:ℝ) with hc | hc
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                  have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1103 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                  have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                  have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                  have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                  have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                  have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · rcases le_total z (2151/2048:ℝ) with hc | hc
            · have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
              have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
              have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1068 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
              have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1105 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2151/2048:ℝ) with hc | hc
            · rcases le_total x (4327/4096:ℝ) with hc | hc
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (239941/400000000000:ℝ) ≤ wfun x := wc_96 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                  have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
                  have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1103 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (239941/400000000000:ℝ) ≤ wfun x := wc_96 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                  have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                  have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_507 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1123 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
              have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1133 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (2021/1024:ℝ) with hc | hc
    · rcases le_total z (1073/1024:ℝ) with hc | hc
      · rcases le_total x (2171/2048:ℝ) with hc | hc
        · rcases le_total y (4037/2048:ℝ) with hc | hc
          · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
            have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_927 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
            have hw5 : (262917659/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_970 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (5858063/1000000000000:ℝ) ≤ wfun x := wc_99 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
          have hw3 : (27892031/5000000000000:ℝ) ≤ wfun (x + y) := wc_452 (x + y) (by linarith) (by linarith)
          have hw5 : (655719053/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_971 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total x (2171/2048:ℝ) with hc | hc
        · rcases le_total y (4037/2048:ℝ) with hc | hc
          · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
            have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1015 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
            have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1069 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (5858063/1000000000000:ℝ) ≤ wfun x := wc_99 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw3 : (27892031/5000000000000:ℝ) ≤ wfun (x + y) := wc_452 (x + y) (by linarith) (by linarith)
          have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1070 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (1073/1024:ℝ) with hc | hc
      · rcases le_total x (2171/2048:ℝ) with hc | hc
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
            have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
            have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1015 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (2141/2048:ℝ) with hc | hc
            · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
              have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
              have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1068 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
              have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
              have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
              have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1105 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · have hw0 : (5858063/1000000000000:ℝ) ≤ wfun x := wc_99 x (by linarith) (by linarith)
            have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
            have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1069 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (5858063/1000000000000:ℝ) ≤ wfun x := wc_99 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
            have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1106 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (2171/2048:ℝ) with hc | hc
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
            have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
            have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_362 (y + z) (by linarith) (by linarith)
            have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1106 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
            have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_390 (y + z) (by linarith) (by linarith)
            have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1134 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (5858063/1000000000000:ℝ) ≤ wfun x := wc_99 x (by linarith) (by linarith)
          have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_518 (x + y) (by linarith) (by linarith)
          have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
          have hw5 : (1787757479/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1135 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_171 (x y z : ℝ) (hx1 : (539/512:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (1023/512:ℝ) with hc | hc
  · rcases le_total z (529/512:ℝ) with hc | hc
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
          have hw5 : (198537007/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_878 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
          have hw5 : (37329233/312500000000:ℝ) ≤ wfun (x + y + z) := wc_930 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
        have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_565 (x + y) (by linarith) (by linarith)
        have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_931 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
                have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_362 (y + z) (by linarith) (by linarith)
                have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1015 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_390 (y + z) (by linarith) (by linarith)
                have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1069 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_561 (x + y) (by linarith) (by linarith)
              have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
              have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1070 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
                  have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                  have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1105 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (326592691/10000000000000:ℝ) ≤ wfun (x + y) := wc_551 (x + y) (by linarith) (by linarith)
                    have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                    have hw5 : (1798491653/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1132 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (365741913/10000000000000:ℝ) ≤ wfun (x + y) := wc_559 (x + y) (by linarith) (by linarith)
                    have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                    have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1142 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                  have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                  have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1133 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                  have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                  have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1148 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_420 (y + z) (by linarith) (by linarith)
                have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1134 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_562 (x + y) (by linarith) (by linarith)
                have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_452 (y + z) (by linarith) (by linarith)
                have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1149 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
            have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
            have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1108 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4087/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_562 (x + y) (by linarith) (by linarith)
                have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_482 (y + z) (by linarith) (by linarith)
                have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1149 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (148228771/2500000000000:ℝ) ≤ wfun (x + y) := wc_566 (x + y) (by linarith) (by linarith)
                have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_518 (y + z) (by linarith) (by linarith)
                have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1165 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_567 (x + y) (by linarith) (by linarith)
              have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
              have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1166 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
            have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
            have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1108 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
            have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
            have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1151 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
            have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
            have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1151 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
            have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1172 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (529/512:ℝ) with hc | hc
    · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
        rcases le_total y (2:ℝ) with hq10 | hq10
        · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
      have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
      have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1020 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2051/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
            have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1151 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
            have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_533 (y + z) (by linarith) (by linarith)
            have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1172 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
          have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_534 (y + z) (by linarith) (by linarith)
          have hw5 : (271686247/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1173 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
        have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_581 (x + y) (by linarith) (by linarith)
        have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
        have hw5 : (216315697/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1174 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_173 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (2041/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (4077/2048:ℝ) with hc | hc
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8149/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8549/8192:ℝ) with hc | hc
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                  have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8559/8192:ℝ) with hc | hc
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                  have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8559/8192:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                  have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                  have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                  have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (8149/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8559/8192:ℝ) with hc | hc
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                  have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                  have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                  have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (19230721/1000000000000:ℝ) ≤ wfun (x + y) := wc_528 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
              have hw5 : (335458679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1101 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
              have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (25929173/1250000000000:ℝ) ≤ wfun (x + y) := wc_535 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
              have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8149/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8569/8192:ℝ) with hc | hc
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                  have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
                  have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8569/8192:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                  have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                  have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                  have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                  have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                  have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
                  have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (82024953/5000000000000:ℝ) ≤ wfun (x + y) := wc_522 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (180388897/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1129 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (35580319/2000000000000:ℝ) ≤ wfun (x + y) := wc_526 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (8149/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (183730059/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1136 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (183730059/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1136 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (93494683/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1138 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (19230721/1000000000000:ℝ) ≤ wfun (x + y) := wc_528 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (180388897/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1129 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (19230721/1000000000000:ℝ) ≤ wfun (x + y) := wc_528 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (1868773189/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1139 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (950804677/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1144 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8159/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (19230721/1000000000000:ℝ) ≤ wfun (x + y) := wc_528 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
              have hw5 : (335458679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1101 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
              have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (19230721/1000000000000:ℝ) ≤ wfun (x + y) := wc_528 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (43501511/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1120 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
            have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8159/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
            have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
            have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
            have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
            have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
            have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
            have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8159/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (19230721/1000000000000:ℝ) ≤ wfun (x + y) := wc_528 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (180388897/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1129 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
            have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
            have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
            have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
            have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
            have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8159/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
            have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
            have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
            have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
            have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
            have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
            have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
            have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
            have hw5 : (2000486673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1158 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_181 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (17/16:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (131/128:ℝ) with hc | hc
  · rcases le_total y (257/128:ℝ) with hc | hc
    · rcases le_total z (141/128:ℝ) with hc | hc
      · rcases le_total x (257/256:ℝ) with hc | hc
        · have hw0 : (12267823741/5000000000000:ℝ) ≤ wfun x := by
            rcases le_total x (1:ℝ) with hq00 | hq00
            · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_6 x (by linarith) (by linarith))
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_134 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
          have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_103 z (by linarith) (by linarith)
          have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
            rcases le_total (x + y) (3:ℝ) with hq30 | hq30
            · exact le_trans (by norm_num) (wc_302 (x + y) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_327 (x + y) (by linarith) (by linarith))
          have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_489 (y + z) (by linarith) (by linarith)
          have hw5 : (59421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_134 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
          have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_103 z (by linarith) (by linarith)
          have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_489 (y + z) (by linarith) (by linarith)
          have hw5 : (153865963/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_788 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
          rcases le_total x (1:ℝ) with hq00 | hq00
          · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_134 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
        have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_108 z (by linarith) (by linarith)
        have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
        have hw5 : (913271/15625000000:ℝ) ≤ wfun (x + y + z) := wc_832 (x + y + z) (by linarith) (by linarith)
        linarith
    · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
        rcases le_total x (1:ℝ) with hq00 | hq00
        · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
      have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_104 z (by linarith) (by linarith)
      have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_594 (y + z) (by linarith) (by linarith)
      have hw5 : (563044583/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_833 (x + y + z) (by linarith) (by linarith)
      linarith
  · rcases le_total y (257/128:ℝ) with hc | hc
    · rcases le_total z (141/128:ℝ) with hc | hc
      · rcases le_total x (267/256:ℝ) with hc | hc
        · rcases le_total y (509/256:ℝ) with hc | hc
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total x (529/512:ℝ) with hc | hc
              · rcases le_total y (1013/512:ℝ) with hc | hc
                · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                  have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_321 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_327 (x + y) (by linarith) (by linarith))
                  have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_486 (y + z) (by linarith) (by linarith)
                  have hw5 : (315273331/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_827 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                  have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_557 (y + z) (by linarith) (by linarith)
                  have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (1013/512:ℝ) with hc | hc
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total x (1063/1024:ℝ) with hc | hc
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                      have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                      have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                      have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_879 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total y (2021/1024:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                        have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
                        have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_484 (y + z) (by linarith) (by linarith)
                        have hw5 : (37329233/312500000000:ℝ) ≤ wfun (x + y + z) := wc_930 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                        have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_534 (y + z) (by linarith) (by linarith)
                        have hw5 : (1413886087/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1018 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_106 z (by linarith) (by linarith)
                    have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                    have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1020 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total x (1063/1024:ℝ) with hc | hc
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                      have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                      have hw5 : (703570097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1019 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total y (2031/1024:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                        have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_555 (y + z) (by linarith) (by linarith)
                        have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1109 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                        have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                        have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
                        have hw5 : (951861201/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1152 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_106 z (by linarith) (by linarith)
                    have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                    have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1154 (x + y + z) (by linarith) (by linarith)
                    linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_107 z (by linarith) (by linarith)
              have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
              have hw5 : (1361028853/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1023 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                have hw5 : (274801629/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1022 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (1023/512:ℝ) with hc | hc
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total x (1063/1024:ℝ) with hc | hc
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                      have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                      have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_364 (x + y) (by linarith) (by linarith)
                      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                      have hw5 : (947330549/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1153 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                      have hw3 : (28290747/10000000000000:ℝ) ≤ wfun (x + y) := wc_422 (x + y) (by linarith) (by linarith)
                      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                      have hw5 : (216315697/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1174 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                    have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_106 z (by linarith) (by linarith)
                    have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                    have hw4 : (591930551/5000000000000:ℝ) ≤ wfun (y + z) := wc_584 (y + z) (by linarith) (by linarith)
                    have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1182 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
                  have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_585 (y + z) (by linarith) (by linarith)
                  have hw5 : (2413024171/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1183 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_107 z (by linarith) (by linarith)
              have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_590 (y + z) (by linarith) (by linarith)
              have hw5 : (591952751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1184 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (509/256:ℝ) with hc | hc
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total y (1013/512:ℝ) with hc | hc
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · rcases le_total y (2021/1024:ℝ) with hc | hc
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                        have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                        have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_484 (y + z) (by linarith) (by linarith)
                        have hw5 : (1413886087/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1018 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                        have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                        have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_534 (y + z) (by linarith) (by linarith)
                        have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1109 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total y (2021/1024:ℝ) with hc | hc
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                        have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                        have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_484 (y + z) (by linarith) (by linarith)
                        have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1109 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                        have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                        have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                        have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_534 (y + z) (by linarith) (by linarith)
                        have hw5 : (951861201/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1152 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                    have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_106 z (by linarith) (by linarith)
                    have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                    have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1154 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · rcases le_total y (2031/1024:ℝ) with hc | hc
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                        have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                        have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                        have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_555 (y + z) (by linarith) (by linarith)
                        have hw5 : (951861201/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1152 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                        have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
                        have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
                        have hw5 : (271686247/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1173 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                      have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                      have hw3 : (28290747/10000000000000:ℝ) ≤ wfun (x + y) := wc_422 (x + y) (by linarith) (by linarith)
                      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                      have hw5 : (216315697/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1174 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                    have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_106 z (by linarith) (by linarith)
                    have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                    have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                    have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1182 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (1013/512:ℝ) with hc | hc
                · have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                  have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_486 (y + z) (by linarith) (by linarith)
                  have hw5 : (933899467/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1155 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
                  have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_557 (y + z) (by linarith) (by linarith)
                  have hw5 : (2413024171/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1183 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_107 z (by linarith) (by linarith)
              have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
              have hw5 : (591952751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1184 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total y (1023/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
                  have hw4 : (676941261/10000000000000:ℝ) ≤ wfun (y + z) := wc_573 (y + z) (by linarith) (by linarith)
                  have hw5 : (2413024171/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1183 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_556 (x + y) (by linarith) (by linarith)
                  have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_585 (y + z) (by linarith) (by linarith)
                  have hw5 : (3019797449/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1194 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_557 (x + y) (by linarith) (by linarith)
                have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                have hw5 : (2991406031/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1195 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_107 z (by linarith) (by linarith)
              have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_487 (x + y) (by linarith) (by linarith)
              have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_590 (y + z) (by linarith) (by linarith)
              have hw5 : (1808088631/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1196 (x + y + z) (by linarith) (by linarith)
              linarith
      · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_134 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
        have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_108 z (by linarith) (by linarith)
        have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
        have hw5 : (2238382569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1187 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (141/128:ℝ) with hc | hc
      · rcases le_total x (267/256:ℝ) with hc | hc
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
          have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_103 z (by linarith) (by linarith)
          have hw3 : (21491553/2500000000000:ℝ) ≤ wfun (x + y) := wc_488 (x + y) (by linarith) (by linarith)
          have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
          have hw5 : (18244153/80000000000:ℝ) ≤ wfun (x + y + z) := wc_1186 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_103 z (by linarith) (by linarith)
          have hw3 : (162913869/2500000000000:ℝ) ≤ wfun (x + y) := wc_576 (x + y) (by linarith) (by linarith)
          have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
          have hw5 : (1741738127/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1198 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_108 z (by linarith) (by linarith)
        have hw3 : (20953831/2500000000000:ℝ) ≤ wfun (x + y) := wc_489 (x + y) (by linarith) (by linarith)
        have hw4 : (5096134953/10000000000000:ℝ) ≤ wfun (y + z) := wc_604 (y + z) (by linarith) (by linarith)
        have hw5 : (600628743/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1199 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_185 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (63/32:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
  linarith

set_option maxHeartbeats 20000000 in
lemma ch_193 (x y z : ℝ) (hx1 : (17/16:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (63/32:ℝ) with hc | hc
  · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_104 x (by linarith) (by linarith)
    have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
    linarith
  · rcases le_total z (63/32:ℝ) with hc | hc
    · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_104 x (by linarith) (by linarith)
      have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
      have hw3 : (75856633/10000000000000:ℝ) ≤ wfun (x + y) := wc_492 (x + y) (by linarith) (by linarith)
      linarith
    · rcases le_total x (141/128:ℝ) with hc | hc
      · rcases le_total y (257/128:ℝ) with hc | hc
        · rcases le_total z (257/128:ℝ) with hc | hc
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total y (509/256:ℝ) with hc | hc
              · rcases le_total z (509/256:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                  have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                  have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                  have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_487 (x + y) (by linarith) (by linarith)
                  have hw4 : (319416431/5000000000000:ℝ) ≤ wfun (y + z) := wc_627 (y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1013/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
                      have hw4 : (71867913/2000000000000:ℝ) ≤ wfun (y + z) := wc_631 (y + z) (by linarith) (by linarith)
                      have hw5 : (3568011/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1220 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                      have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_556 (x + y) (by linarith) (by linarith)
                      have hw4 : (157670757/10000000000000:ℝ) ≤ wfun (y + z) := wc_636 (y + z) (by linarith) (by linarith)
                      have hw5 : (38680157/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1241 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_106 x (by linarith) (by linarith)
                    have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                    have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_557 (x + y) (by linarith) (by linarith)
                    have hw4 : (31317919/2000000000000:ℝ) ≤ wfun (y + z) := wc_632 (y + z) (by linarith) (by linarith)
                    have hw5 : (76765783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1242 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (509/256:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
                  have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                  have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
                  have hw4 : (31317919/2000000000000:ℝ) ≤ wfun (y + z) := wc_632 (y + z) (by linarith) (by linarith)
                  have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1222 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1023/512:ℝ) with hc | hc
                    · rcases le_total z (1023/512:ℝ) with hc | hc
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                        have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
                        have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                        have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                        have hw4 : (39629583/2500000000000:ℝ) ≤ wfun (y + z) := wc_642 (y + z) (by linarith) (by linarith)
                        have hw5 : (191511939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1266 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                        have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
                        have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                          rcases le_total z (2:ℝ) with hq20 | hq20
                          · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                        have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                        have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_650 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_668 (y + z) (by linarith) (by linarith))
                        have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1314 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                      have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1315 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_106 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                    have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
                    have hw5 : (43578037/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1316 (x + y + z) (by linarith) (by linarith)
                    linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_107 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_134 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
              have hw3 : (162913869/2500000000000:ℝ) ≤ wfun (x + y) := wc_576 (x + y) (by linarith) (by linarith)
              have hw5 : (6814137/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1224 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total y (509/256:ℝ) with hc | hc
              · rcases le_total z (519/256:ℝ) with hc | hc
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1013/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                      have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
                      have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_643 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_668 (y + z) (by linarith) (by linarith))
                      have hw5 : (190040129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1267 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                      have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                      have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_556 (x + y) (by linarith) (by linarith)
                      have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1315 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_106 x (by linarith) (by linarith)
                    have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                    have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_557 (x + y) (by linarith) (by linarith)
                    have hw5 : (43578037/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1316 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                  have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                  have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_487 (x + y) (by linarith) (by linarith)
                  have hw5 : (551493311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1372 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (519/256:ℝ) with hc | hc
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1023/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                      have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                      have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1370 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                      have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                      have hw5 : (814792219/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1434 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_106 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                    have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
                    have hw5 : (404289107/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1435 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
                  have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
                  have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_702 (y + z) (by linarith) (by linarith)
                  have hw5 : (1097277581/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1472 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_107 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_134 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
              have hw3 : (162913869/2500000000000:ℝ) ≤ wfun (x + y) := wc_576 (x + y) (by linarith) (by linarith)
              have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1374 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (257/128:ℝ) with hc | hc
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total y (519/256:ℝ) with hc | hc
              · rcases le_total z (509/256:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                  have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_244 y (by linarith) (by linarith)
                  have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                  have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_590 (x + y) (by linarith) (by linarith)
                  have hw5 : (187138697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1269 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                  have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_244 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_590 (x + y) (by linarith) (by linarith)
                  have hw5 : (551493311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1372 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                have hw3 : (1670535297/5000000000000:ℝ) ≤ wfun (x + y) := wc_598 (x + y) (by linarith) (by linarith)
                have hw5 : (108627463/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1373 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_107 x (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
              have hw3 : (1629257293/5000000000000:ℝ) ≤ wfun (x + y) := wc_599 (x + y) (by linarith) (by linarith)
              have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1374 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
            have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_592 (x + y) (by linarith) (by linarith)
            have hw4 : (60567/10000000000000:ℝ) ≤ wfun (y + z) := wc_705 (y + z) (by linarith) (by linarith)
            have hw5 : (1048517003/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1474 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_108 x (by linarith) (by linarith)
        have hw3 : (798582451/5000000000000:ℝ) ≤ wfun (x + y) := wc_594 (x + y) (by linarith) (by linarith)
        have hw5 : (168305763/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1273 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_196 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (179/64:ℝ) ≤ z) (hz2 : z ≤ (105/32:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (389/128:ℝ) with hc | hc
  · rcases le_total y (131/64:ℝ) with hc | hc
    · rcases le_total z (747/256:ℝ) with hc | hc
      · have hw2 : (1457053011/2000000000000:ℝ) ≤ wfun z := wc_287 z (by linarith) (by linarith)
        have hw4 : (498772193/10000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (19/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_1208 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_1209 (y + z) (by linarith) (by linarith))
        linarith
      · rcases le_total x (17/16:ℝ) with hc | hc
        · rcases le_total y (63/32:ℝ) with hc | hc
          · have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
            have hw4 : (533121/1000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (5:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_1211 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_1212 (y + z) (by linarith) (by linarith))
            linarith
          · linarith
        · linarith
    · linarith
  · linarith

set_option maxHeartbeats 20000000 in
lemma ch_200 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (747/256:ℝ) ≤ y) (hy2 : y ≤ (3019/1024:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (267/256:ℝ) with hc | hc
  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
    have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_291 y (by linarith) (by linarith)
    have hw3 : (122092393/5000000000000:ℝ) ≤ wfun (x + y) := wc_629 (x + y) (by linarith) (by linarith)
    have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
      · exact le_trans (by norm_num) (wc_630 (y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_673 (y + z) (by linarith) (by linarith))
    linarith
  · rcases le_total z (267/256:ℝ) with hc | hc
    · have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_291 y (by linarith) (by linarith)
      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
      have hw3 : (436723/500000000000:ℝ) ≤ wfun (x + y) := by
        rcases le_total (x + y) (4:ℝ) with hq30 | hq30
        · exact le_trans (by norm_num) (wc_634 (x + y) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_673 (x + y) (by linarith) (by linarith))
      have hw4 : (122092393/5000000000000:ℝ) ≤ wfun (y + z) := wc_629 (y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total y (6007/2048:ℝ) with hc | hc
      · have hw1 : (2995265257/5000000000000:ℝ) ≤ wfun y := wc_290 y (by linarith) (by linarith)
        have hw3 : (82600037/5000000000000:ℝ) ≤ wfun (x + y) := wc_633 (x + y) (by linarith) (by linarith)
        have hw4 : (82600037/5000000000000:ℝ) ≤ wfun (y + z) := wc_633 (y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (539/512:ℝ) with hc | hc
        · rcases le_total z (539/512:ℝ) with hc | hc
          · rcases le_total y (12045/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (2512351653/5000000000000:ℝ) ≤ wfun y := wc_293 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
              have hw3 : (103153789/5000000000000:ℝ) ≤ wfun (x + y) := wc_639 (x + y) (by linarith) (by linarith)
              have hw4 : (103153789/5000000000000:ℝ) ≤ wfun (y + z) := wc_639 (y + z) (by linarith) (by linarith)
              have hw5 : (12553451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1216 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (821878027/2000000000000:ℝ) ≤ wfun y := wc_295 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
              have hw3 : (11042139/1250000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_647 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_661 (x + y) (by linarith) (by linarith))
              have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_647 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_661 (y + z) (by linarith) (by linarith))
              have hw5 : (55553319/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1235 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (12045/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (2512351653/5000000000000:ℝ) ≤ wfun y := wc_293 y (by linarith) (by linarith)
              have hw3 : (103153789/5000000000000:ℝ) ≤ wfun (x + y) := wc_639 (x + y) (by linarith) (by linarith)
              have hw4 : (6315177/1000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_648 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_664 (y + z) (by linarith) (by linarith))
              have hw5 : (73715499/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1236 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (821878027/2000000000000:ℝ) ≤ wfun y := wc_295 y (by linarith) (by linarith)
              have hw3 : (11042139/1250000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_647 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_661 (x + y) (by linarith) (by linarith))
              have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_654 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_673 (y + z) (by linarith) (by linarith))
              have hw5 : (155628467/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1256 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (539/512:ℝ) with hc | hc
          · rcases le_total y (12045/4096:ℝ) with hc | hc
            · have hw1 : (2512351653/5000000000000:ℝ) ≤ wfun y := wc_293 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
              have hw3 : (6315177/1000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_648 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_664 (x + y) (by linarith) (by linarith))
              have hw4 : (103153789/5000000000000:ℝ) ≤ wfun (y + z) := wc_639 (y + z) (by linarith) (by linarith)
              have hw5 : (73715499/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1236 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (821878027/2000000000000:ℝ) ≤ wfun y := wc_295 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
              have hw3 : (436723/500000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_654 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_673 (x + y) (by linarith) (by linarith))
              have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_647 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_661 (y + z) (by linarith) (by linarith))
              have hw5 : (155628467/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1256 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (12045/4096:ℝ) with hc | hc
            · have hw1 : (2512351653/5000000000000:ℝ) ≤ wfun y := wc_293 y (by linarith) (by linarith)
              have hw3 : (6315177/1000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_648 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_664 (x + y) (by linarith) (by linarith))
              have hw4 : (6315177/1000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_648 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_664 (y + z) (by linarith) (by linarith))
              have hw5 : (46245893/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1259 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (821878027/2000000000000:ℝ) ≤ wfun y := wc_295 y (by linarith) (by linarith)
              have hw3 : (436723/500000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_654 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_673 (x + y) (by linarith) (by linarith))
              have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_654 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_673 (y + z) (by linarith) (by linarith))
              have hw5 : (76262343/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1299 (x + y + z) (by linarith) (by linarith)
              linarith

end Zeta23Ext.Bridge.FourPoint
