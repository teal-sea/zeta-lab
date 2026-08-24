import FourPoint.Cells

/-! Chunk module 12 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_6 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (131/128:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
      · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
    have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
      rcases le_total z (1:ℝ) with hq20 | hq20
      · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
    linarith
  · rcases le_total y (509/256:ℝ) with hc | hc
    · have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
      have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
        rcases le_total z (1:ℝ) with hq20 | hq20
        · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_198 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
      linarith
    · rcases le_total z (257/256:ℝ) with hc | hc
      · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
        have hw2 : (12267823741/5000000000000:ℝ) ≤ wfun z := by
          rcases le_total z (1:ℝ) with hq20 | hq20
          · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_6 z (by linarith) (by linarith))
        have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (3:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_208 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
        have hw5 : (3087/500000000000:ℝ) ≤ wfun (x + y + z) := wc_455 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
        have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := wc_9 z (by linarith) (by linarith)
        have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
        have hw5 : (159841537/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_512 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_7 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (529/512:ℝ) with hc | hc
  · rcases le_total y (1013/512:ℝ) with hc | hc
    · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
      have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
        rcases le_total (x + y) (3:ℝ) with hq30 | hq30
        · exact le_trans (by norm_num) (wc_215 (x + y) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
      have hw5 : (31471/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_453 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total z (529/512:ℝ) with hc | hc
      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
        have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw5 : (10750333/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_492 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (1053/1024:ℝ) with hc | hc
        · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
          have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_224 (x + y) (by linarith) (by linarith)
          have hw5 : (165310021/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_508 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (2031/1024:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
            have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
            have hw5 : (128356097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_520 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
            have hw5 : (183260287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_528 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total y (1013/512:ℝ) with hc | hc
    · rcases le_total z (529/512:ℝ) with hc | hc
      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
        have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (3:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
        have hw5 : (10750333/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_492 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (1063/1024:ℝ) with hc | hc
        · rcases le_total y (2021/1024:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
            have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_223 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_224 (y + z) (by linarith) (by linarith)
            have hw5 : (8305511/500000000000:ℝ) ≤ wfun (x + y + z) := wc_507 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
              have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
              have hw5 : (128977417/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_519 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
              have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
              have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_527 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (2021/1024:ℝ) with hc | hc
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
              have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
              have hw5 : (128977417/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_519 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_227 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
                have hw5 : (184591317/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_526 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_230 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
                have hw5 : (431662129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_534 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
              have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_527 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · rcases le_total y (4047/2048:ℝ) with hc | hc
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
                  have hw5 : (20003551/400000000000:ℝ) ≤ wfun (x + y + z) := wc_535 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                  have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                  have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_540 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (4047/2048:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
                  have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_540 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                    have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_542 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                    linarith
    · rcases le_total z (529/512:ℝ) with hc | hc
      · rcases le_total x (1063/1024:ℝ) with hc | hc
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
          have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw5 : (165310021/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_508 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (2031/1024:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
            have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_224 (y + z) (by linarith) (by linarith)
            have hw5 : (128356097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_520 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
            have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
            have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
            have hw5 : (183260287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_528 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (1063/1024:ℝ) with hc | hc
        · rcases le_total y (2031/1024:ℝ) with hc | hc
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
              have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_527 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2121/2048:ℝ) with hc | hc
              · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
                have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_232 (x + y) (by linarith) (by linarith)
                have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_536 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (4057/2048:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                  have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_540 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_543 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
              have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_537 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2121/2048:ℝ) with hc | hc
              · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
                have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
                have hw5 : (323709737/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_544 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (4067/2048:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                  have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                  have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_243 (y + z) (by linarith) (by linarith)
                  have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_558 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                    have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                    have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                    have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                    have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                    have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                    have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                    linarith
        · rcases le_total y (2031/1024:ℝ) with hc | hc
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_536 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (4057/2048:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
                  have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_540 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                  have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                  have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_543 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · rcases le_total y (4057/2048:ℝ) with hc | hc
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_542 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                    have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (4057/2048:ℝ) with hc | hc
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_559 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_238 (x + y) (by linarith) (by linarith)
                      have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_568 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                    have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_241 (x + y) (by linarith) (by linarith)
                      have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                      have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_570 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total y (8119/4096:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                        have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
                        have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                        have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
                        have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
                        linarith
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                have hw3 : (235547/2000000000000:ℝ) ≤ wfun (x + y) := wc_243 (x + y) (by linarith) (by linarith)
                have hw5 : (323709737/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_544 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (4067/2048:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                  have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                  have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                  have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_558 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (2121/2048:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                    have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
                    have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                    have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                    have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                    have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                    have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (2131/2048:ℝ) with hc | hc
              · rcases le_total y (4067/2048:ℝ) with hc | hc
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                    have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (4257/4096:ℝ) with hc | hc
                    · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                      have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_241 (x + y) (by linarith) (by linarith)
                      have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                      have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_570 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                      have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_251 (x + y) (by linarith) (by linarith)
                      have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                      have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_577 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                    have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                    have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                    have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                    have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                    have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (4257/4096:ℝ) with hc | hc
                    · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                      have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
                      have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                      have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_580 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
                      have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                      have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_263 (x + y) (by linarith) (by linarith)
                      have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                      have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_592 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total y (4067/2048:ℝ) with hc | hc
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · rcases le_total x (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                      have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                      have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
                      have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                      have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_570 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                      have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                      have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_263 (x + y) (by linarith) (by linarith)
                      have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                      have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_577 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (4267/4096:ℝ) with hc | hc
                    · rcases le_total y (8129/4096:ℝ) with hc | hc
                      · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                        have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                        have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
                        have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                        have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                        have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
                        have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total y (8129/4096:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                        have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
                        have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total z (4267/4096:ℝ) with hc | hc
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                          have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                          have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                          have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                          have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                          have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                          have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                          have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                          have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                          have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                          linarith
                · rcases le_total z (2131/2048:ℝ) with hc | hc
                  · rcases le_total x (4267/4096:ℝ) with hc | hc
                    · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                      have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                      have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                      have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
                      have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                      have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_580 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                      have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                      have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                      have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_279 (x + y) (by linarith) (by linarith)
                      have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                      have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_592 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (4267/4096:ℝ) with hc | hc
                    · rcases le_total y (8139/4096:ℝ) with hc | hc
                      · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                        have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                        have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
                        have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                        have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                        have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
                        have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total y (8139/4096:ℝ) with hc | hc
                      · rcases le_total z (4267/4096:ℝ) with hc | hc
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                          have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                          have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
                          have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                          have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                          have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                          have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                          have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                          have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                          have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                        have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                        have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                        have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
                        have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
                        linarith

set_option maxHeartbeats 20000000 in
lemma ch_22 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (2021/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (1073/1024:ℝ) with hc | hc
  · rcases le_total x (2141/2048:ℝ) with hc | hc
    · rcases le_total y (4037/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
          have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_542 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
          have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
          have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
          have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (4277/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_233 (x + y) (by linarith) (by linarith)
            have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_559 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_235 (x + y) (by linarith) (by linarith)
            have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_568 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (4037/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
          have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (4287/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_233 (x + y) (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
            have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_559 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_235 (x + y) (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
            have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_568 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4287/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
            have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_559 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
            have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_568 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (4287/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_236 (x + y) (by linarith) (by linarith)
              have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_569 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (2141/2048:ℝ) with hc | hc
    · rcases le_total y (4037/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
          have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
          have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4277/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_233 (x + y) (by linarith) (by linarith)
            have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_570 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_235 (x + y) (by linarith) (by linarith)
            have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_577 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (4277/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_233 (x + y) (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
            have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_580 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_235 (x + y) (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
            have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_592 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (4037/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4287/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_233 (x + y) (by linarith) (by linarith)
            have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_570 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_235 (x + y) (by linarith) (by linarith)
            have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_577 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
          have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4287/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_236 (x + y) (by linarith) (by linarith)
              have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
              have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4287/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
            have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_596 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_36 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
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
    · rcases le_total y (4067/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
                  have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                  have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
                  have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
                  have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                  have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
                  have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                  have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_314 (x + y) (by linarith) (by linarith)
                  have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                  have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_317 (x + y) (by linarith) (by linarith)
                  have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                  have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
                  have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                  have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
                  have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                  have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
                  have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                  have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
                  have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                  have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_314 (x + y) (by linarith) (by linarith)
                  have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                  have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_317 (x + y) (by linarith) (by linarith)
                  have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                  have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_314 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                  have hw5 : (335458679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_684 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_317 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                  have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_694 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8599/8192:ℝ) with hc | hc
                · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_314 (x + y) (by linarith) (by linarith)
                  have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                  have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_317 (x + y) (by linarith) (by linarith)
                  have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                  have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_705 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (4067/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
              have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
              have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
              have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
              have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
              have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
              have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
              have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
              have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
              have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
              have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
              have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
              have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_332 (x + y) (by linarith) (by linarith)
              have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
              have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
              have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
              have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
              have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
              have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
              have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
              have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_332 (x + y) (by linarith) (by linarith)
              have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
              have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_708 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (2151/2048:ℝ) with hc | hc
    · rcases le_total y (4067/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · rcases le_total x (8589/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                  have hw5 : (335458679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_684 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                  have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                  have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_694 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_705 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
              have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
              have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
              have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
              have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_708 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_705 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
              have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
              have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
              have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
              have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_708 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_319 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
            have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_709 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
            have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_721 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (4067/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
              have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
              have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
              have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
              have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
              have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
              have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
              have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
              have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_708 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_319 (x + y) (by linarith) (by linarith)
            have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
            have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_709 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
            have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
            have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_721 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
              have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
              have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_708 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
              have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_720 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_331 (x + y) (by linarith) (by linarith)
            have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
            have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_721 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
          have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
          have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
          have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
          have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_58 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (131/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (17/16:ℝ) with hc | hc
  · rcases le_total y (63/32:ℝ) with hc | hc
    · have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_76 y (by linarith) (by linarith)
      have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_160 z (by linarith) (by linarith)
      linarith
    · rcases le_total z (17/8:ℝ) with hc | hc
      · rcases le_total x (131/128:ℝ) with hc | hc
        · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
            rcases le_total x (1:ℝ) with hq00 | hq00
            · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
          have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
          have hw4 : (56143/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (257/128:ℝ) with hc | hc
          · rcases le_total z (267/128:ℝ) with hc | hc
            · rcases le_total x (267/256:ℝ) with hc | hc
              · rcases le_total y (509/256:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
                  have hw2 : (18186303/400000000000:ℝ) ≤ wfun z := wc_156 z (by linarith) (by linarith)
                  have hw4 : (3087/500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                  have hw5 : (5759139/312500000000:ℝ) ≤ wfun (x + y + z) := wc_811 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                  have hw2 : (18186303/400000000000:ℝ) ≤ wfun z := wc_156 z (by linarith) (by linarith)
                  have hw4 : (159841537/10000000000000:ℝ) ≤ wfun (y + z) := wc_512 (y + z) (by linarith) (by linarith)
                  have hw5 : (108627463/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (509/256:ℝ) with hc | hc
                · have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
                  have hw2 : (18186303/400000000000:ℝ) ≤ wfun z := wc_156 z (by linarith) (by linarith)
                  have hw4 : (3087/500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                  have hw5 : (108627463/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                  have hw2 : (18186303/400000000000:ℝ) ≤ wfun z := wc_156 z (by linarith) (by linarith)
                  have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
                  have hw4 : (159841537/10000000000000:ℝ) ≤ wfun (y + z) := wc_512 (y + z) (by linarith) (by linarith)
                  have hw5 : (270178737/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_948 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
              have hw2 : (4789633321/10000000000000:ℝ) ≤ wfun z := wc_172 z (by linarith) (by linarith)
              have hw4 : (24278963/400000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
              have hw5 : (1048517003/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
            have hw3 : (20953831/2500000000000:ℝ) ≤ wfun (x + y) := wc_308 (x + y) (by linarith) (by linarith)
            have hw4 : (913271/15625000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
            have hw5 : (1017509707/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw2 : (48584483/40000000000:ℝ) ≤ wfun z := wc_178 z (by linarith) (by linarith)
        have hw4 : (2156990541/10000000000000:ℝ) ≤ wfun (y + z) := wc_742 (y + z) (by linarith) (by linarith)
        have hw5 : (502714163/5000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_951 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_974 (x + y + z) (by linarith) (by linarith))
        linarith
  · rcases le_total y (63/32:ℝ) with hc | hc
    · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
      have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_76 y (by linarith) (by linarith)
      have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_160 z (by linarith) (by linarith)
      linarith
    · rcases le_total z (17/8:ℝ) with hc | hc
      · rcases le_total x (141/128:ℝ) with hc | hc
        · rcases le_total y (257/128:ℝ) with hc | hc
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
            have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
            have hw3 : (20953831/2500000000000:ℝ) ≤ wfun (x + y) := wc_308 (x + y) (by linarith) (by linarith)
            have hw4 : (58303/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
            have hw5 : (1017509707/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
            have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (913271/15625000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
            have hw5 : (1266297497/5000000000000:ℝ) ≤ wfun (x + y + z) := by
              rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
              · exact le_trans (by norm_num) (wc_968 (x + y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_972 (x + y + z) (by linarith) (by linarith))
            linarith
        · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
          have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
          have hw3 : (798582451/5000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
          have hw4 : (56143/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
          have hw5 : (1266297497/5000000000000:ℝ) ≤ wfun (x + y + z) := by
            rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
            · exact le_trans (by norm_num) (wc_968 (x + y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_974 (x + y + z) (by linarith) (by linarith))
          linarith
      · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
        have hw2 : (48584483/40000000000:ℝ) ≤ wfun z := wc_178 z (by linarith) (by linarith)
        have hw3 : (75856633/10000000000000:ℝ) ≤ wfun (x + y) := wc_311 (x + y) (by linarith) (by linarith)
        have hw4 : (2156990541/10000000000000:ℝ) ≤ wfun (y + z) := wc_742 (y + z) (by linarith) (by linarith)
        have hw5 : (2343009541/5000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_970 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_977 (x + y + z) (by linarith) (by linarith))
        linarith

end Zeta23Ext.Bridge.FourPoint
