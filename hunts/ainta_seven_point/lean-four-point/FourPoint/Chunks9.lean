import FourPoint.Cells

/-! Chunk module 9 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_9 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (63/32:ℝ))
    (hz1 : (17/16:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (131/128:ℝ) with hc | hc
  · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
      rcases le_total x (1:ℝ) with hq00 | hq00
      · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
    have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
    have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_104 z (by linarith) (by linarith)
    have hw3 : (269743281/5000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
    linarith
  · rcases le_total y (247/128:ℝ) with hc | hc
    · have hw1 : (9113139537/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
      have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_104 z (by linarith) (by linarith)
      have hw3 : (288828359/5000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
      linarith
    · rcases le_total z (141/128:ℝ) with hc | hc
      · rcases le_total x (267/256:ℝ) with hc | hc
        · rcases le_total y (499/256:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
            have hw1 : (6028900351/5000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
            have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_103 z (by linarith) (by linarith)
            have hw3 : (15105971/250000000000:ℝ) ≤ wfun (x + y) := wc_301 (x + y) (by linarith) (by linarith)
            have hw5 : (60567/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_705 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (688065547/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                have hw3 : (13065663/500000000000:ℝ) ≤ wfun (x + y) := by
                  rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                  · exact le_trans (by norm_num) (wc_312 (x + y) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_324 (x + y) (by linarith) (by linarith))
                have hw5 : (20172571/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_785 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (1003/512:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                  have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw3 : (13065663/500000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_319 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_324 (x + y) (by linarith) (by linarith))
                  have hw5 : (89884553/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_806 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                  have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_321 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_327 (x + y) (by linarith) (by linarith))
                  have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                  have hw5 : (315273331/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_827 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (688065547/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_107 z (by linarith) (by linarith)
              have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_312 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_327 (x + y) (by linarith) (by linarith))
              have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_487 (y + z) (by linarith) (by linarith)
              have hw5 : (154654989/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_829 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (499/256:ℝ) with hc | hc
          · have hw1 : (6028900351/5000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
            have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_103 z (by linarith) (by linarith)
            have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
              rcases le_total (x + y) (3:ℝ) with hq30 | hq30
              · exact le_trans (by norm_num) (wc_312 (x + y) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_327 (x + y) (by linarith) (by linarith))
            have hw5 : (39204539/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_787 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total y (1003/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                  have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_321 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_327 (x + y) (by linarith) (by linarith))
                  have hw5 : (315273331/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_827 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                      have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                      have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                      have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                      have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_879 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                      have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_101 z (by linarith) (by linarith)
                      have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                      have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_931 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                    have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_106 z (by linarith) (by linarith)
                    have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                    have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1020 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (1003/512:ℝ) with hc | hc
                · have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                  have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                  have hw5 : (69357131/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1021 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw1 : (688065547/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_107 z (by linarith) (by linarith)
              have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_487 (y + z) (by linarith) (by linarith)
              have hw5 : (1361028853/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1023 (x + y + z) (by linarith) (by linarith)
              linarith
      · have hw1 : (6731724963/10000000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
        have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_108 z (by linarith) (by linarith)
        have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_489 (y + z) (by linarith) (by linarith)
        have hw5 : (913271/15625000000:ℝ) ≤ wfun (x + y + z) := wc_832 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_11 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (131/128:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (267/256:ℝ) with hc | hc
  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
      rcases le_total y (2:ℝ) with hq10 | hq10
      · exact le_trans (by norm_num) (wc_134 y (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
    have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
      rcases le_total z (1:ℝ) with hq20 | hq20
      · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
    linarith
  · rcases le_total y (509/256:ℝ) with hc | hc
    · have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
      have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
        rcases le_total z (1:ℝ) with hq20 | hq20
        · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_302 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
      linarith
    · rcases le_total z (257/256:ℝ) with hc | hc
      · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
        have hw2 : (12267823741/5000000000000:ℝ) ≤ wfun z := by
          rcases le_total z (1:ℝ) with hq20 | hq20
          · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_6 z (by linarith) (by linarith))
        have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_487 (x + y) (by linarith) (by linarith)
        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (3:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_312 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
        have hw5 : (3087/500000000000:ℝ) ≤ wfun (x + y + z) := wc_704 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
        have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := wc_9 z (by linarith) (by linarith)
        have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_487 (x + y) (by linarith) (by linarith)
        have hw5 : (159841537/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_786 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_13 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (529/512:ℝ) with hc | hc
  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
    have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
    have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
      rcases le_total (y + z) (3:ℝ) with hq40 | hq40
      · exact le_trans (by norm_num) (wc_321 (y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
    have hw5 : (10750333/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_759 (x + y + z) (by linarith) (by linarith)
    linarith
  · rcases le_total x (1063/1024:ℝ) with hc | hc
    · rcases le_total y (2021/1024:ℝ) with hc | hc
      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
        have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
        have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_330 (y + z) (by linarith) (by linarith)
        have hw5 : (8305511/500000000000:ℝ) ≤ wfun (x + y + z) := wc_781 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
          have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
          have hw5 : (128977417/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (2121/2048:ℝ) with hc | hc
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
            have hw5 : (184591317/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_801 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_337 (x + y) (by linarith) (by linarith)
            have hw5 : (431662129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_810 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (2021/1024:ℝ) with hc | hc
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
          have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
          have hw5 : (128977417/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
            have hw5 : (184591317/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_801 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (4037/2048:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_336 (x + y) (by linarith) (by linarith)
              have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (432705303/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_809 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_337 (y + z) (by linarith) (by linarith)
              have hw5 : (20003551/400000000000:ℝ) ≤ wfun (x + y + z) := wc_811 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (1063/1024:ℝ) with hc | hc
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
            have hw5 : (184591317/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_801 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
            have hw5 : (431662129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_810 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
              have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
              have hw5 : (20003551/400000000000:ℝ) ≤ wfun (x + y + z) := wc_811 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                have hw5 : (573574207/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_816 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (4047/2048:ℝ) with hc | hc
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
                have hw5 : (573574207/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_816 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                  have hw5 : (325666339/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_819 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                  have hw5 : (69161783/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_835 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (2131/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (4267/4096:ℝ) with hc | hc
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw5 : (14661301/200000000000:ℝ) ≤ wfun (x + y + z) := wc_838 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (8099/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw5 : (388302571/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw5 : (820415059/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                    linarith

set_option maxHeartbeats 20000000 in
lemma ch_20 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (1063/1024:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (2031/1024:ℝ) with hc | hc
  · rcases le_total z (1073/1024:ℝ) with hc | hc
    · rcases le_total x (2121/2048:ℝ) with hc | hc
      · rcases le_total y (4057/2048:ℝ) with hc | hc
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
          have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
          have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_362 (y + z) (by linarith) (by linarith)
          have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_821 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
          have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
          have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_390 (y + z) (by linarith) (by linarith)
          have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (4057/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
            have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (4247/4096:ℝ) with hc | hc
            · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
              have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
              have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_856 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4247/4096:ℝ) with hc | hc
            · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
              have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
              have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_856 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4247/4096:ℝ) with hc | hc
            · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
              have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
              have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (2121/2048:ℝ) with hc | hc
      · rcases le_total y (4057/2048:ℝ) with hc | hc
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
          have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
          have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_420 (y + z) (by linarith) (by linarith)
          have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_848 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
          have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
          have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_452 (y + z) (by linarith) (by linarith)
          have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (4057/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4247/4096:ℝ) with hc | hc
            · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
              have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
              have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
            have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4247/4096:ℝ) with hc | hc
            · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
              have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_873 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
              have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_889 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
            have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (1073/1024:ℝ) with hc | hc
    · rcases le_total x (2121/2048:ℝ) with hc | hc
      · rcases le_total y (4067/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
            have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
            have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
            have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
            have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
            have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
            have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (4067/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4247/4096:ℝ) with hc | hc
            · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
              have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
              have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4247/4096:ℝ) with hc | hc
            · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
              have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_873 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (8129/4096:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_466 (y + z) (by linarith) (by linarith)
                have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4247/4096:ℝ) with hc | hc
            · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
              have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
              have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_873 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (8139/4096:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_466 (y + z) (by linarith) (by linarith)
                have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4247/4096:ℝ) with hc | hc
            · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
              have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
              have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_898 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (8139/4096:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
                have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_507 (y + z) (by linarith) (by linarith)
                have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (2121/2048:ℝ) with hc | hc
      · rcases le_total y (4067/2048:ℝ) with hc | hc
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
          have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_482 (y + z) (by linarith) (by linarith)
          have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_875 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
          have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_518 (y + z) (by linarith) (by linarith)
          have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_900 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (4067/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4247/4096:ℝ) with hc | hc
            · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
              have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_898 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
              have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
              have hw5 : (1157601093/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_911 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
            have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4247/4096:ℝ) with hc | hc
            · have hw0 : (1676998161/5000000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
              have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
              have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_925 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_375 (x + y) (by linarith) (by linarith)
              have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
              have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_948 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
            have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_54 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (1063/1024:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (2151/2048:ℝ) with hc | hc
  · rcases le_total y (4067/2048:ℝ) with hc | hc
    · rcases le_total z (2131/2048:ℝ) with hc | hc
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4257/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
              have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4257/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4257/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
              have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4257/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                  have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
                  have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                  have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
                  have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                  have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
                  have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                  have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
                  have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · rcases le_total z (8539/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                    have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                    have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                    have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                    have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                    have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                    have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                    have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (8539/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                    have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                    have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                    have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                    have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                    have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                    have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                    have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · rcases le_total z (8539/8192:ℝ) with hc | hc
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                    have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                    have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                    have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                    have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                    have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                    have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                    have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (8539/8192:ℝ) with hc | hc
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                    have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                    have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                    have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                    have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                    have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                    have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                    have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16263/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                  have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
                  have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                  have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16263/8192:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                  have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16263/8192:ℝ) with hc | hc
                · rcases le_total z (8539/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                    have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                    have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                    have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                    have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                    have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                    have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                    have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (8539/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                    have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                    have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                    have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                    have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                    have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                    have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                    have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (16263/8192:ℝ) with hc | hc
                · rcases le_total z (8539/8192:ℝ) with hc | hc
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                    have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                    have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                    have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                    have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                    have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                    have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                    have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                  have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
                  have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                  have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_511 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1001 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · rcases le_total z (8539/8192:ℝ) with hc | hc
                  · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                    have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                    have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                    have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                    have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                    have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                    have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                    have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                    have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                    have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                  have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                  have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (138011869/10000000000000:ℝ) ≤ wfun (x + y) := wc_514 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1010 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · rcases le_total y (16263/8192:ℝ) with hc | hc
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                  have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16263/8192:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                  have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                  have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
                  have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                  linarith
    · rcases le_total z (2131/2048:ℝ) with hc | hc
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4257/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4257/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4257/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4257/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16273/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                  have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16273/8192:ℝ) with hc | hc
                · rcases le_total z (8539/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                    have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                    have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                    have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                    have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                    have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                    have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                    have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                  have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16273/8192:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                  have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                  have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                  have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (82024953/5000000000000:ℝ) ≤ wfun (x + y) := wc_522 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (35580319/2000000000000:ℝ) ≤ wfun (x + y) := wc_526 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16283/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                  have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                  have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                  have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                  have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
                  have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16283/8192:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                  have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                  have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                  have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                  have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
                  have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (82024953/5000000000000:ℝ) ≤ wfun (x + y) := wc_522 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (35580319/2000000000000:ℝ) ≤ wfun (x + y) := wc_526 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · rcases le_total y (16273/8192:ℝ) with hc | hc
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                  have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                  have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
                  have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                  have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
                  have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
                  have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (35580319/2000000000000:ℝ) ≤ wfun (x + y) := wc_526 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (19230721/1000000000000:ℝ) ≤ wfun (x + y) := wc_528 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total y (4067/2048:ℝ) with hc | hc
    · rcases le_total z (2131/2048:ℝ) with hc | hc
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4257/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4257/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
            have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
            have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
            have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_375 (y + z) (by linarith) (by linarith)
            have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8609/8192:ℝ) with hc | hc
              · rcases le_total y (16253/8192:ℝ) with hc | hc
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                  have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                  have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8609/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (82024953/5000000000000:ℝ) ≤ wfun (x + y) := wc_522 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (35580319/2000000000000:ℝ) ≤ wfun (x + y) := wc_526 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (2131/2048:ℝ) with hc | hc
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
            have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
            have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
            have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
            have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
            have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
            have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
            have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8609/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (19230721/1000000000000:ℝ) ≤ wfun (x + y) := wc_528 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4267/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_55 (x y z : ℝ) (hx1 : (539/512:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (1013/512:ℝ) with hc | hc
  · rcases le_total z (529/512:ℝ) with hc | hc
    · have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_321 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
      have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2021/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
            have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_823 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4037/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
                  have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_333 (y + z) (by linarith) (by linarith)
                  have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
                  have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
                  have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
                  have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
                  have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
                  have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
                  have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4037/2048:ℝ) with hc | hc
              · have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_337 (y + z) (by linarith) (by linarith)
                have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_875 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_848 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_337 (y + z) (by linarith) (by linarith)
                have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw3 : (27892031/5000000000000:ℝ) ≤ wfun (x + y) := wc_452 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
              have hw5 : (45246083/500000000000:ℝ) ≤ wfun (x + y + z) := wc_862 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
                  have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
                  have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8089/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                      have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                      have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                      have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                      have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                      have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                      have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_436 (x + y) (by linarith) (by linarith)
                    have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                    have hw5 : (1157601093/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_911 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                  have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8099/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                      have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                      have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                      have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (8099/4096:ℝ) with hc | hc
                    · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                      have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                      have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                      have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                      linarith
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
                  have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
                  have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                  have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                  have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                  have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total y (2021/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
            have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_850 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
            have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
            have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
            have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (2171/2048:ℝ) with hc | hc
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_927 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
                have hw5 : (262917659/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_970 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (5858063/1000000000000:ℝ) ≤ wfun x := wc_99 x (by linarith) (by linarith)
              have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_518 (x + y) (by linarith) (by linarith)
              have hw5 : (655719053/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_971 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (529/512:ℝ) with hc | hc
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_330 (y + z) (by linarith) (by linarith)
          have hw5 : (160690591/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_824 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
          have hw5 : (808657969/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_851 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
        have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_534 (x + y) (by linarith) (by linarith)
        have hw5 : (402392913/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_852 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_875 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (2121/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                  have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                  have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
                  have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_900 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
                have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_927 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (5774823/625000000000:ℝ) ≤ wfun (x + y) := wc_480 (x + y) (by linarith) (by linarith)
                    have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_925 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_507 (x + y) (by linarith) (by linarith)
                    have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_948 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8109/4096:ℝ) with hc | hc
                    · rcases le_total z (4267/4096:ℝ) with hc | hc
                      · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                        have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                        have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                        have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                        have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                        have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                        have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                        have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total z (4267/4096:ℝ) with hc | hc
                      · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                        have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                        have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                        have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                        have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
                        have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                        have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                        have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                        have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total y (8109/4096:ℝ) with hc | hc
                    · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                      have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                      have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                      have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                      have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
                      have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8119/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                      have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                      have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                      have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                      have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                      have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
                      have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
                      have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_524 (x + y) (by linarith) (by linarith)
                    have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_992 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8119/4096:ℝ) with hc | hc
                    · rcases le_total z (4267/4096:ℝ) with hc | hc
                      · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                        have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                        have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                        have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                        have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
                        have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                        have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                        have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                        have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total z (4267/4096:ℝ) with hc | hc
                      · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                        have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                        have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                        have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
                        have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
                        have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                        have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
                        have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                        have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total y (8119/4096:ℝ) with hc | hc
                    · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                      have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
                      have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
                      have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                      have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
                      have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_375 (y + z) (by linarith) (by linarith)
                      have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
                      linarith
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
                  have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
                  have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1014 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
                  have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1014 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
                  have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1068 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · rcases le_total z (2121/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                  have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
                  have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
                  have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
                have hw5 : (262917659/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_970 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
                have hw5 : (262917659/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_970 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
                have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1015 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (47960431/2500000000000:ℝ) ≤ wfun (x + y) := wc_530 (x + y) (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                    have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1013 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_540 (x + y) (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                    have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1046 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8129/4096:ℝ) with hc | hc
                    · rcases le_total z (4267/4096:ℝ) with hc | hc
                      · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                        have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                        have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                        have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
                        have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
                        have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                        have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                        have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
                        have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
                        have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                      have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                      have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                      have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1087 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (8129/4096:ℝ) with hc | hc
                    · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                      have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                      have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
                      have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1087 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                      have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                      have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                      have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1103 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1068 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8139/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                      have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                      have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                      have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1103 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                      have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                      have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                      have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                      have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                    have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_549 (x + y) (by linarith) (by linarith)
                    have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                    have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1123 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
                  have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1068 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                  have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1105 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                  have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1105 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                  have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
                  have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                  have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1133 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
            have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_929 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (2171/2048:ℝ) with hc | hc
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
                have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1015 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
                have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1069 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (5858063/1000000000000:ℝ) ≤ wfun x := wc_99 x (by linarith) (by linarith)
              have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_545 (x + y) (by linarith) (by linarith)
              have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1070 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
            have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
            have hw5 : (1420672477/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1017 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (2171/2048:ℝ) with hc | hc
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
                have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
                have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_362 (y + z) (by linarith) (by linarith)
                have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1106 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_97 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_210 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_390 (y + z) (by linarith) (by linarith)
                have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1134 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (5858063/1000000000000:ℝ) ≤ wfun x := wc_99 x (by linarith) (by linarith)
              have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_561 (x + y) (by linarith) (by linarith)
              have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
              have hw5 : (1787757479/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1135 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_66 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (4047/2048:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (2151/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8099/4096:ℝ) with hc | hc
  · rcases le_total z (4297/4096:ℝ) with hc | hc
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
            have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (2641873/10000000000000:ℝ) ≤ wfun (x + y) := wc_367 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (716733/2000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (2641873/10000000000000:ℝ) ≤ wfun (x + y) := wc_367 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (716733/2000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (2641873/10000000000000:ℝ) ≤ wfun (x + y) := wc_367 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (716733/2000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (4297/4096:ℝ) with hc | hc
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (7269931/10000000000000:ℝ) ≤ wfun (x + y) := wc_377 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_76 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (4047/2048:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (2151/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4297/4096:ℝ) with hc | hc
  · rcases le_total y (8099/4096:ℝ) with hc | hc
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32401/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                  have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                  have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                  have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                  have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32401/16384:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                  have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                  have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                  have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                  have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32411/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                  have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                  have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                  have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                  have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32411/16384:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                  have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                  have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                  have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                  have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · rcases le_total y (32411/16384:ℝ) with hc | hc
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                  have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                  have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                  have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                  have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                  have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32411/16384:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                  have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                  have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                  have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                  have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                  have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · rcases le_total y (32401/16384:ℝ) with hc | hc
                · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                  have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                  have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                  have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                  have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                  have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                  have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · rcases le_total y (32411/16384:ℝ) with hc | hc
                · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                  have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                  have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                  have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                  have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                  have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                  have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32411/16384:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                  have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                  have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                  have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                  have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                  have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                  have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (8099/4096:ℝ) with hc | hc
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17193/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
            have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17193/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17193/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17193/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17193/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17203/16384:ℝ) with hc | hc
              · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_103 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (8119/4096:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (4287/4096:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (8569/8192:ℝ) with hc | hc
  · rcases le_total y (16243/8192:ℝ) with hc | hc
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32481/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32481/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32481/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32481/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32491/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32491/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32491/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
            have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
            have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
            have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
            have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (32491/16384:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
            have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
            have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
            have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
            have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total y (16243/8192:ℝ) with hc | hc
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32481/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32481/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
              have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32481/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32481/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
              have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8579/8192:ℝ) with hc | hc
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32491/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32491/16384:ℝ) with hc | hc
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
              have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17153/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
              have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32491/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
              have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (19508469/2500000000000:ℝ) ≤ wfun (y + z) := wc_467 (y + z) (by linarith) (by linarith)
              have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
            have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
            have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (32491/16384:ℝ) with hc | hc
          · rcases le_total z (17163/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (73402187/10000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
              have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (19508469/2500000000000:ℝ) ≤ wfun (y + z) := wc_467 (y + z) (by linarith) (by linarith)
              have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
            have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
            have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_111 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (2151/2048:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4277/4096:ℝ) with hc | hc
  · rcases le_total y (8119/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
            have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
            have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
            have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
            have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
            have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
            have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
          have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
          have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
          have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
          have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
          have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
          have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
          have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
          have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
          have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
          have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total y (8119/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_416 (x + y) (by linarith) (by linarith)
          have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
          have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_428 (x + y) (by linarith) (by linarith)
          have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
          have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_132 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (4067/2048:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4287/4096:ℝ) with hc | hc
  · rcases le_total y (8139/4096:ℝ) with hc | hc
    · rcases le_total z (4287/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4287/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (16418259/1000000000000:ℝ) ≤ wfun (y + z) := wc_521 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (16418259/1000000000000:ℝ) ≤ wfun (y + z) := wc_521 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (8139/4096:ℝ) with hc | hc
    · rcases le_total z (4287/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · rcases le_total x (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (62990037/5000000000000:ℝ) ≤ wfun (x + y) := wc_509 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (66005017/5000000000000:ℝ) ≤ wfun (x + y) := wc_512 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (62990037/5000000000000:ℝ) ≤ wfun (x + y) := wc_509 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (66005017/5000000000000:ℝ) ≤ wfun (x + y) := wc_512 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4287/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8569/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
            have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
            have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8579/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (1806053569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1127 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
            have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
            have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_138 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (4297/4096:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (4057/2048:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (2141/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8109/4096:ℝ) with hc | hc
  · rcases le_total z (4277/4096:ℝ) with hc | hc
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total z (4277/4096:ℝ) with hc | hc
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_186 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (131/128:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (63/32:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
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
  linarith

set_option maxHeartbeats 20000000 in
lemma ch_192 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (257/128:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (63/32:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (257/128:ℝ) with hc | hc
  · rcases le_total x (267/256:ℝ) with hc | hc
    · rcases le_total y (519/256:ℝ) with hc | hc
      · rcases le_total z (509/256:ℝ) with hc | hc
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_244 y (by linarith) (by linarith)
            have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
            have hw3 : (22330933/2500000000000:ℝ) ≤ wfun (x + y) := wc_486 (x + y) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_244 y (by linarith) (by linarith)
            have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
            have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_557 (x + y) (by linarith) (by linarith)
            linarith
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_244 y (by linarith) (by linarith)
            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
              rcases le_total z (2:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
            have hw3 : (22330933/2500000000000:ℝ) ≤ wfun (x + y) := wc_486 (x + y) (by linarith) (by linarith)
            have hw5 : (14162149/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1221 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1023/512:ℝ) with hc | hc
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                  have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_555 (x + y) (by linarith) (by linarith)
                  have hw5 : (19565737/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1239 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                  have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_565 (x + y) (by linarith) (by linarith)
                  have hw5 : (129046413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1250 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_555 (x + y) (by linarith) (by linarith)
                  have hw5 : (19225319/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1265 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (2051/1024:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_235 z (by linarith) (by linarith))
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                      have hw5 : (134914401/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1288 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_239 z (by linarith) (by linarith)
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                      have hw5 : (358152183/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1310 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                    have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1312 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (1023/512:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw5 : (191511939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1266 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (172511147/2500000000000:ℝ) ≤ wfun (x + y) := wc_571 (x + y) (by linarith) (by linarith)
                  have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_700 (y + z) (by linarith) (by linarith)
                  have hw5 : (71079411/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1313 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                  have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_581 (x + y) (by linarith) (by linarith)
                  have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_700 (y + z) (by linarith) (by linarith)
                  have hw5 : (91007427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1341 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total z (509/256:ℝ) with hc | hc
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
          have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
          have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1222 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
              rcases le_total z (2:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
            have hw3 : (676941261/10000000000000:ℝ) ≤ wfun (x + y) := wc_573 (x + y) (by linarith) (by linarith)
            have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_702 (y + z) (by linarith) (by linarith)
            have hw5 : (37716487/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1268 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
              rcases le_total z (2:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
            have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
            have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_702 (y + z) (by linarith) (by linarith)
            have hw5 : (43578037/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1316 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (519/256:ℝ) with hc | hc
      · rcases le_total z (509/256:ℝ) with hc | hc
        · rcases le_total x (539/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1013/512:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw2 : (4884069333/10000000000000:ℝ) ≤ wfun z := wc_132 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw4 : (39629583/2500000000000:ℝ) ≤ wfun (y + z) := wc_642 (y + z) (by linarith) (by linarith)
                have hw5 : (449469/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1219 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw2 : (3192232409/10000000000000:ℝ) ≤ wfun z := wc_165 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_650 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_668 (y + z) (by linarith) (by linarith))
                have hw5 : (38980307/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1240 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
              have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
              have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
              have hw5 : (38680157/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1241 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_244 y (by linarith) (by linarith)
            have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
            have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
            have hw5 : (76765783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1242 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (539/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1023/512:ℝ) with hc | hc
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                    have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                    have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                    have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_673 (y + z) (by linarith) (by linarith))
                    have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1264 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                    have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                    have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1290 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                    have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                    have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                    have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                    have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_673 (y + z) (by linarith) (by linarith))
                    have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1290 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                    have hw3 : (9367789/78125000000:ℝ) ≤ wfun (x + y) := wc_582 (x + y) (by linarith) (by linarith)
                    have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1312 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (2051/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_235 z (by linarith) (by linarith))
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                      have hw5 : (358152183/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1310 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total x (2141/2048:ℝ) with hc | hc
                      · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                        have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                        have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_239 z (by linarith) (by linarith)
                        have hw3 : (27868611/400000000000:ℝ) ≤ wfun (x + y) := wc_569 (x + y) (by linarith) (by linarith)
                        have hw5 : (11486191/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1337 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                        have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                        have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_239 z (by linarith) (by linarith)
                        have hw3 : (81082719/1000000000000:ℝ) ≤ wfun (x + y) := wc_579 (x + y) (by linarith) (by linarith)
                        have hw5 : (257119041/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1355 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                    have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                    have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1340 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (2051/1024:ℝ) with hc | hc
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_235 z (by linarith) (by linarith))
                      have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                      have hw5 : (458561277/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1338 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_239 z (by linarith) (by linarith)
                      have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                      have hw5 : (114178013/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1366 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                    have hw3 : (9367789/78125000000:ℝ) ≤ wfun (x + y) := wc_582 (x + y) (by linarith) (by linarith)
                    have hw5 : (568693187/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1367 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (1023/512:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1314 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (297859663/2500000000000:ℝ) ≤ wfun (x + y) := wc_583 (x + y) (by linarith) (by linarith)
                  have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_700 (y + z) (by linarith) (by linarith)
                  have hw5 : (566506871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1368 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                  have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (298142111/2000000000000:ℝ) ≤ wfun (x + y) := wc_588 (x + y) (by linarith) (by linarith)
                  have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_700 (y + z) (by linarith) (by linarith)
                  have hw5 : (68963139/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1401 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1023/512:ℝ) with hc | hc
              · have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1314 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1369 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
              have hw3 : (1810022563/10000000000000:ℝ) ≤ wfun (x + y) := wc_589 (x + y) (by linarith) (by linarith)
              have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1370 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (509/256:ℝ) with hc | hc
        · have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
          have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_590 (x + y) (by linarith) (by linarith)
          have hw5 : (187138697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1269 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
            rcases le_total z (2:ℝ) with hq20 | hq20
            · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
          have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_590 (x + y) (by linarith) (by linarith)
          have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_702 (y + z) (by linarith) (by linarith)
          have hw5 : (551493311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1372 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total x (267/256:ℝ) with hc | hc
    · rcases le_total y (519/256:ℝ) with hc | hc
      · rcases le_total z (519/256:ℝ) with hc | hc
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_244 y (by linarith) (by linarith)
            have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
            have hw3 : (22330933/2500000000000:ℝ) ≤ wfun (x + y) := wc_486 (x + y) (by linarith) (by linarith)
            have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_702 (y + z) (by linarith) (by linarith)
            have hw5 : (37716487/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1268 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1033/512:ℝ) with hc | hc
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                  have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_555 (x + y) (by linarith) (by linarith)
                  have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_700 (y + z) (by linarith) (by linarith)
                  have hw5 : (71079411/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1313 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (2061/1024:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                      have hw4 : (64801/10000000000000:ℝ) ≤ wfun (y + z) := wc_698 (y + z) (by linarith) (by linarith)
                      have hw5 : (458561277/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1338 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_246 z (by linarith) (by linarith)
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                      have hw4 : (11849221/10000000000000:ℝ) ≤ wfun (y + z) := wc_733 (y + z) (by linarith) (by linarith)
                      have hw5 : (114178013/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1366 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                    have hw4 : (11791793/10000000000000:ℝ) ≤ wfun (y + z) := wc_734 (y + z) (by linarith) (by linarith)
                    have hw5 : (568693187/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1367 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                  have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_555 (x + y) (by linarith) (by linarith)
                  have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_757 (y + z) (by linarith) (by linarith)
                  have hw5 : (566506871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1368 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                  have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_565 (x + y) (by linarith) (by linarith)
                  have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_757 (y + z) (by linarith) (by linarith)
                  have hw5 : (68963139/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1401 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (1033/512:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_757 (y + z) (by linarith) (by linarith)
                have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1369 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw4 : (8305511/500000000000:ℝ) ≤ wfun (y + z) := wc_781 (y + z) (by linarith) (by linarith)
                have hw5 : (821066057/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1433 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_244 y (by linarith) (by linarith)
            have hw3 : (22330933/2500000000000:ℝ) ≤ wfun (x + y) := wc_486 (x + y) (by linarith) (by linarith)
            have hw4 : (81469089/5000000000000:ℝ) ≤ wfun (y + z) := wc_784 (y + z) (by linarith) (by linarith)
            have hw5 : (69466449/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1371 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_244 y (by linarith) (by linarith)
            have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_557 (x + y) (by linarith) (by linarith)
            have hw4 : (81469089/5000000000000:ℝ) ≤ wfun (y + z) := wc_784 (y + z) (by linarith) (by linarith)
            have hw5 : (404289107/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1435 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (519/256:ℝ) with hc | hc
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
            have hw3 : (676941261/10000000000000:ℝ) ≤ wfun (x + y) := wc_573 (x + y) (by linarith) (by linarith)
            have hw4 : (81469089/5000000000000:ℝ) ≤ wfun (y + z) := wc_784 (y + z) (by linarith) (by linarith)
            have hw5 : (69466449/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1371 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
            have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
            have hw4 : (81469089/5000000000000:ℝ) ≤ wfun (y + z) := wc_784 (y + z) (by linarith) (by linarith)
            have hw5 : (404289107/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1435 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
          have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
          have hw4 : (315273331/5000000000000:ℝ) ≤ wfun (y + z) := wc_827 (y + z) (by linarith) (by linarith)
          have hw5 : (1097277581/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1472 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (519/256:ℝ) with hc | hc
      · rcases le_total z (519/256:ℝ) with hc | hc
        · rcases le_total x (539/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1033/512:ℝ) with hc | hc
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (2061/1024:ℝ) with hc | hc
                    · rcases le_total x (2141/2048:ℝ) with hc | hc
                      · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                        have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                        have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                        have hw3 : (27868611/400000000000:ℝ) ≤ wfun (x + y) := wc_569 (x + y) (by linarith) (by linarith)
                        have hw4 : (64801/10000000000000:ℝ) ≤ wfun (y + z) := wc_698 (y + z) (by linarith) (by linarith)
                        have hw5 : (571992483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1365 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                        have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                        have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                        have hw3 : (81082719/1000000000000:ℝ) ≤ wfun (x + y) := wc_579 (x + y) (by linarith) (by linarith)
                        have hw4 : (64801/10000000000000:ℝ) ≤ wfun (y + z) := wc_698 (y + z) (by linarith) (by linarith)
                        have hw5 : (316344203/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1387 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_246 z (by linarith) (by linarith)
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                      have hw4 : (11849221/10000000000000:ℝ) ≤ wfun (y + z) := wc_733 (y + z) (by linarith) (by linarith)
                      have hw5 : (694962061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1399 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                    have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                    have hw4 : (11791793/10000000000000:ℝ) ≤ wfun (y + z) := wc_734 (y + z) (by linarith) (by linarith)
                    have hw5 : (692290309/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1400 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (2061/1024:ℝ) with hc | hc
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                      have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                      have hw4 : (64801/10000000000000:ℝ) ≤ wfun (y + z) := wc_698 (y + z) (by linarith) (by linarith)
                      have hw5 : (694962061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1399 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_242 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_246 z (by linarith) (by linarith)
                      have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                      have hw4 : (11849221/10000000000000:ℝ) ≤ wfun (y + z) := wc_733 (y + z) (by linarith) (by linarith)
                      have hw5 : (830590517/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1430 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_246 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                    have hw3 : (9367789/78125000000:ℝ) ≤ wfun (x + y) := wc_582 (x + y) (by linarith) (by linarith)
                    have hw4 : (11791793/10000000000000:ℝ) ≤ wfun (y + z) := wc_734 (y + z) (by linarith) (by linarith)
                    have hw5 : (827400419/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1431 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                  have hw3 : (172511147/2500000000000:ℝ) ≤ wfun (x + y) := wc_571 (x + y) (by linarith) (by linarith)
                  have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_757 (y + z) (by linarith) (by linarith)
                  have hw5 : (824225629/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1432 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                  have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_581 (x + y) (by linarith) (by linarith)
                  have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_757 (y + z) (by linarith) (by linarith)
                  have hw5 : (194018909/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1456 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (1033/512:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_757 (y + z) (by linarith) (by linarith)
                have hw5 : (821066057/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1433 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (8305511/500000000000:ℝ) ≤ wfun (y + z) := wc_781 (y + z) (by linarith) (by linarith)
                have hw5 : (140340159/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1470 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1033/512:ℝ) with hc | hc
              · have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_700 (y + z) (by linarith) (by linarith)
                have hw5 : (821066057/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1433 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_243 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_757 (y + z) (by linarith) (by linarith)
                have hw5 : (140340159/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1470 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_248 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
              have hw3 : (1810022563/10000000000000:ℝ) ≤ wfun (x + y) := wc_589 (x + y) (by linarith) (by linarith)
              have hw4 : (10750333/2500000000000:ℝ) ≤ wfun (y + z) := wc_759 (y + z) (by linarith) (by linarith)
              have hw5 : (1114158849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1471 (x + y + z) (by linarith) (by linarith)
              linarith
        · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_244 y (by linarith) (by linarith)
          have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
          have hw4 : (81469089/5000000000000:ℝ) ≤ wfun (y + z) := wc_784 (y + z) (by linarith) (by linarith)
          have hw5 : (1097277581/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1472 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_590 (x + y) (by linarith) (by linarith)
        have hw4 : (159841537/10000000000000:ℝ) ≤ wfun (y + z) := wc_786 (y + z) (by linarith) (by linarith)
        have hw5 : (270178737/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1473 (x + y + z) (by linarith) (by linarith)
        linarith

end Zeta23Ext.Bridge.FourPoint
