import FourPoint.Cells

/-! Chunk module 1 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_13 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (539/512:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1063/1024:ℝ) with hc | hc
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2121/2048:ℝ) with hc | hc
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
          have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_232 (x + y) (by linarith) (by linarith)
          have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
          have hw5 : (199972023/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_583 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
          have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
          have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
          have hw5 : (549643007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_599 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
        have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
        have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
        have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_613 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2121/2048:ℝ) with hc | hc
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
          have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
          have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
          have hw5 : (1203159081/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_612 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
          have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
          have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
          have hw5 : (655719053/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_633 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
        have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
        have hw5 : (1420672477/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_651 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2131/2048:ℝ) with hc | hc
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_301 (y + z) (by linarith) (by linarith)
            have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_611 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_321 (y + z) (by linarith) (by linarith)
            have hw5 : (262917659/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_632 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (4057/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                have hw5 : (659665673/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_630 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_238 (x + y) (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_640 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
              have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
              have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_648 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_241 (x + y) (by linarith) (by linarith)
                have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_647 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_251 (x + y) (by linarith) (by linarith)
                have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_666 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
              have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
              have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (2131/2048:ℝ) with hc | hc
        · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
          have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
          have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
          have hw5 : (1424080951/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_650 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
          have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
          have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
          have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_676 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2131/2048:ℝ) with hc | hc
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
            have hw4 : (7636599/400000000000:ℝ) ≤ wfun (y + z) := wc_327 (y + z) (by linarith) (by linarith)
            have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_649 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
            have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
            have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_675 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (4067/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
              have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
              have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
              have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_688 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
            have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
            have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_689 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
        have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
        have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
        have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_26 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (2021/1024:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (1073/1024:ℝ) with hc | hc
  · rcases le_total x (2151/2048:ℝ) with hc | hc
    · rcases le_total y (4047/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                  have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                  have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_617 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                  have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                  have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                  have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_617 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                  have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                  have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_624 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                  have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                  have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_624 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                  have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                  have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                  have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                  have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8599/8192:ℝ) with hc | hc
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                  have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                  have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                  have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8599/8192:ℝ) with hc | hc
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                  have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                  have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                  have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                  have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                  linarith
    · rcases le_total y (4047/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
              have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_237 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
              have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total x (2151/2048:ℝ) with hc | hc
    · rcases le_total y (4047/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
              have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
              have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
              have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                  have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                  have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                  have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                  have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                  have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                  have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                  have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                  have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                  have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                  have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                  have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · rcases le_total x (8599/8192:ℝ) with hc | hc
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                  have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                  have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                  have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4307/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
              have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
              have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (4047/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
              have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
              have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8089/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
              have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
            have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_263 (x + y) (by linarith) (by linarith)
            have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
            have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_666 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
              have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
              have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
              have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
              have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8099/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
              have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
              have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_35 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (2151/2048:ℝ) with hc | hc
  · rcases le_total y (4057/2048:ℝ) with hc | hc
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
            have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
            have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
            have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
            have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
            have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
            have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
            have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
            have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
            have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
            have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total y (4057/2048:ℝ) with hc | hc
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
            have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
            have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
            have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
            have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
            have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
            have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
            have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
            have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
          have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
          have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_293 (x + y) (by linarith) (by linarith)
          have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
          have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_698 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
            have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
            have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
            have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
            have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
            have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
            have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
            have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
            have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
          have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
          have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_316 (x + y) (by linarith) (by linarith)
          have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
          have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_707 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_40 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1023/512:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (529/512:ℝ) with hc | hc
  · rcases le_total x (1073/1024:ℝ) with hc | hc
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · rcases le_total z (1053/1024:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
          have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
          have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
          have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
          have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_584 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
          have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_14 z (by linarith) (by linarith)
          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
          have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
          have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_613 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
        have hw4 : (28290747/10000000000000:ℝ) ≤ wfun (y + z) := wc_273 (y + z) (by linarith) (by linarith)
        have hw5 : (37329233/312500000000:ℝ) ≤ wfun (x + y + z) := wc_614 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
        have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
        have hw4 : (1166349/10000000000000:ℝ) ≤ wfun (y + z) := wc_245 (y + z) (by linarith) (by linarith)
        have hw5 : (37329233/312500000000:ℝ) ≤ wfun (x + y + z) := wc_614 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
        have hw4 : (28290747/10000000000000:ℝ) ≤ wfun (y + z) := wc_273 (y + z) (by linarith) (by linarith)
        have hw5 : (1413886087/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_652 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total x (1073/1024:ℝ) with hc | hc
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · rcases le_total x (2141/2048:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_341 (x + y) (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
            have hw5 : (1424080951/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_650 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
            have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_676 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (2141/2048:ℝ) with hc | hc
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
                have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_688 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
              have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
              have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_703 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
              have hw4 : (7636599/400000000000:ℝ) ≤ wfun (y + z) := wc_327 (y + z) (by linarith) (by linarith)
              have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_703 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
              have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
              have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_711 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
          have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
          have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
          have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
          have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
          have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
          have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
          have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (2151/2048:ℝ) with hc | hc
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
              have hw4 : (7636599/400000000000:ℝ) ≤ wfun (y + z) := wc_327 (y + z) (by linarith) (by linarith)
              have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_711 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (148228771/2500000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
              have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
              have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_723 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
            have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
            have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
            have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_724 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
          have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
          have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
          have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
          have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_74 (x y z : ℝ) (hx1 : (121/64:ℝ) ≤ x) (hx2 : x ≤ (141/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (179/64:ℝ) ≤ z) (hz2 : z ≤ (105/32:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (389/128:ℝ) with hc | hc
  · rcases le_total x (131/64:ℝ) with hc | hc
    · rcases le_total z (747/256:ℝ) with hc | hc
      · have hw2 : (1457053011/2000000000000:ℝ) ≤ wfun z := wc_187 z (by linarith) (by linarith)
        linarith
      · linarith
    · linarith
  · linarith

end Zeta23Ext.Bridge.FourPoint
