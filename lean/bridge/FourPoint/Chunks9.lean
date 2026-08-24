import FourPoint.Cells

/-! Chunk module 9 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_2 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
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
  · rcases le_total z (747/256:ℝ) with hc | hc
    · have hw2 : (1457053011/2000000000000:ℝ) ≤ wfun z := wc_187 z (by linarith) (by linarith)
      linarith
    · rcases le_total x (17/16:ℝ) with hc | hc
      · rcases le_total y (17/16:ℝ) with hc | hc
        · rcases le_total z (1525/512:ℝ) with hc | hc
          · rcases le_total x (131/128:ℝ) with hc | hc
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw2 : (261299809/2000000000000:ℝ) ≤ wfun z := wc_192 z (by linarith) (by linarith)
              linarith
            · rcases le_total y (131/128:ℝ) with hc | hc
              · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                have hw2 : (261299809/2000000000000:ℝ) ≤ wfun z := wc_192 z (by linarith) (by linarith)
                have hw4 : (76620491/10000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_404 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_433 (y + z) (by linarith) (by linarith))
                linarith
              · rcases le_total z (3019/1024:ℝ) with hc | hc
                · rcases le_total x (267/256:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                    have hw2 : (100676353/250000000000:ℝ) ≤ wfun z := wc_191 z (by linarith) (by linarith)
                    have hw3 : (437829947/10000000000000:ℝ) ≤ wfun (x + y) := wc_157 (x + y) (by linarith) (by linarith)
                    have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_408 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
                    linarith
                  · have hw2 : (100676353/250000000000:ℝ) ≤ wfun z := wc_191 z (by linarith) (by linarith)
                    have hw3 : (2001469121/10000000000000:ℝ) ≤ wfun (x + y) := wc_168 (x + y) (by linarith) (by linarith)
                    have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_408 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
                    linarith
                · rcases le_total x (267/256:ℝ) with hc | hc
                  · rcases le_total y (267/256:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw2 : (67339097/500000000000:ℝ) ≤ wfun z := wc_196 z (by linarith) (by linarith)
                      have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                      have hw2 : (67339097/500000000000:ℝ) ≤ wfun z := wc_196 z (by linarith) (by linarith)
                      have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                      have hw5 : (155031/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_765 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (267/256:ℝ) with hc | hc
                    · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw2 : (67339097/500000000000:ℝ) ≤ wfun z := wc_196 z (by linarith) (by linarith)
                      have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                      have hw5 : (155031/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_765 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw2 : (67339097/500000000000:ℝ) ≤ wfun z := wc_196 z (by linarith) (by linarith)
                      have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_172 (x + y) (by linarith) (by linarith)
                      have hw5 : (2491077/200000000000:ℝ) ≤ wfun (x + y + z) := wc_798 (x + y + z) (by linarith) (by linarith)
                      linarith
          · rcases le_total x (131/128:ℝ) with hc | hc
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              linarith
            · rcases le_total y (131/128:ℝ) with hc | hc
              · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                linarith
              · rcases le_total z (3081/1024:ℝ) with hc | hc
                · rcases le_total x (267/256:ℝ) with hc | hc
                  · rcases le_total y (267/256:ℝ) with hc | hc
                    · rcases le_total z (6131/2048:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw2 : (137922559/2500000000000:ℝ) ≤ wfun z := wc_211 z (by linarith) (by linarith)
                        have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                        have hw5 : (4557569/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_781 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw2 : (102076243/10000000000000:ℝ) ≤ wfun z := by
                          rcases le_total z (3:ℝ) with hq20 | hq20
                          · exact le_trans (by norm_num) (wc_216 z (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                        have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                        have hw4 : (1432423/10000000000000:ℝ) ≤ wfun (y + z) := wc_467 (y + z) (by linarith) (by linarith)
                        have hw5 : (8346273/400000000000:ℝ) ≤ wfun (x + y + z) := wc_818 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                      have hw2 : (102076243/10000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (3:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_212 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                      have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                      have hw4 : (999363/625000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
                      have hw5 : (274435871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_834 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (267/256:ℝ) with hc | hc
                    · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw2 : (102076243/10000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (3:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_212 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                      have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                      have hw5 : (274435871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_834 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw2 : (102076243/10000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (3:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_212 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                      have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_172 (x + y) (by linarith) (by linarith)
                      have hw4 : (999363/625000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
                      have hw5 : (345435191/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total x (267/256:ℝ) with hc | hc
                  · rcases le_total y (267/256:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                      have hw4 : (58750599/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                      have hw5 : (480942433/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_869 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                      have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                      have hw4 : (267941559/5000000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                      have hw5 : (199185017/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw3 : (2001469121/10000000000000:ℝ) ≤ wfun (x + y) := wc_168 (x + y) (by linarith) (by linarith)
                    have hw4 : (7204521/625000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                    have hw5 : (245228749/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
                    linarith
        · rcases le_total z (1525/512:ℝ) with hc | hc
          · rcases le_total x (131/128:ℝ) with hc | hc
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
              have hw2 : (261299809/2000000000000:ℝ) ≤ wfun z := wc_192 z (by linarith) (by linarith)
              have hw3 : (12244337/312500000000:ℝ) ≤ wfun (x + y) := wc_159 (x + y) (by linarith) (by linarith)
              linarith
            · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
              have hw2 : (261299809/2000000000000:ℝ) ≤ wfun z := wc_192 z (by linarith) (by linarith)
              have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_175 (x + y) (by linarith) (by linarith)
              linarith
          · rcases le_total x (131/128:ℝ) with hc | hc
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
              have hw3 : (12244337/312500000000:ℝ) ≤ wfun (x + y) := wc_159 (x + y) (by linarith) (by linarith)
              have hw4 : (246785359/10000000000000:ℝ) ≤ wfun (y + z) := wc_525 (y + z) (by linarith) (by linarith)
              have hw5 : (41391449/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_783 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
              have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_175 (x + y) (by linarith) (by linarith)
              have hw4 : (246785359/10000000000000:ℝ) ≤ wfun (y + z) := wc_525 (y + z) (by linarith) (by linarith)
              have hw5 : (635374807/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (17/16:ℝ) with hc | hc
        · rcases le_total z (1525/512:ℝ) with hc | hc
          · rcases le_total x (141/128:ℝ) with hc | hc
            · rcases le_total y (131/128:ℝ) with hc | hc
              · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                have hw2 : (261299809/2000000000000:ℝ) ≤ wfun z := wc_192 z (by linarith) (by linarith)
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
                have hw4 : (76620491/10000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_404 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_433 (y + z) (by linarith) (by linarith))
                linarith
              · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw2 : (261299809/2000000000000:ℝ) ≤ wfun z := wc_192 z (by linarith) (by linarith)
                have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
                linarith
            · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw2 : (261299809/2000000000000:ℝ) ≤ wfun z := wc_192 z (by linarith) (by linarith)
              have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_175 (x + y) (by linarith) (by linarith)
              linarith
          · rcases le_total x (141/128:ℝ) with hc | hc
            · rcases le_total y (131/128:ℝ) with hc | hc
              · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
                have hw5 : (42660549/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_782 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
                have hw5 : (327353763/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_912 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_175 (x + y) (by linarith) (by linarith)
              have hw5 : (635374807/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
              linarith
        · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
          have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
          have hw3 : (2788858101/2500000000000:ℝ) ≤ wfun (x + y) := by
            rcases le_total (x + y) (9/4:ℝ) with hq30 | hq30
            · exact le_trans (by norm_num) (wc_179 (x + y) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_182 (x + y) (by linarith) (by linarith))
          have hw5 : (109191861/5000000000000:ℝ) ≤ wfun (x + y + z) := by
            rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
            · exact le_trans (by norm_num) (wc_824 (x + y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_975 (x + y + z) (by linarith) (by linarith))
          linarith
  · rcases le_total z (809/256:ℝ) with hc | hc
    · rcases le_total x (17/16:ℝ) with hc | hc
      · rcases le_total y (17/16:ℝ) with hc | hc
        · rcases le_total z (1587/512:ℝ) with hc | hc
          · rcases le_total x (131/128:ℝ) with hc | hc
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw2 : (249212333/10000000000000:ℝ) ≤ wfun z := wc_336 z (by linarith) (by linarith)
              have hw4 : (25235977/10000000000000:ℝ) ≤ wfun (y + z) := wc_486 (y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (131/128:ℝ) with hc | hc
              · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                have hw2 : (249212333/10000000000000:ℝ) ≤ wfun z := wc_336 z (by linarith) (by linarith)
                have hw4 : (13104471/5000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                have hw5 : (72912521/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_837 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw2 : (249212333/10000000000000:ℝ) ≤ wfun z := wc_336 z (by linarith) (by linarith)
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
                have hw4 : (848165913/10000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                have hw5 : (128184591/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
          · have hw2 : (2090005161/5000000000000:ℝ) ≤ wfun z := wc_382 z (by linarith) (by linarith)
            have hw4 : (1697224391/10000000000000:ℝ) ≤ wfun (y + z) := wc_719 (y + z) (by linarith) (by linarith)
            have hw5 : (18241731/250000000000:ℝ) ≤ wfun (x + y + z) := by
              rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
              · exact le_trans (by norm_num) (wc_924 (x + y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_973 (x + y + z) (by linarith) (by linarith))
            linarith
        · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
          have hw2 : (115281189/5000000000000:ℝ) ≤ wfun z := wc_337 z (by linarith) (by linarith)
          have hw3 : (182240171/5000000000000:ℝ) ≤ wfun (x + y) := wc_160 (x + y) (by linarith) (by linarith)
          have hw4 : (2606310863/10000000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (17/4:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_745 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_756 (y + z) (by linarith) (by linarith))
          have hw5 : (1257182497/10000000000000:ℝ) ≤ wfun (x + y + z) := by
            rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
            · exact le_trans (by norm_num) (wc_962 (x + y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_976 (x + y + z) (by linarith) (by linarith))
          linarith
      · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
        have hw2 : (115281189/5000000000000:ℝ) ≤ wfun z := wc_337 z (by linarith) (by linarith)
        have hw3 : (167375901/5000000000000:ℝ) ≤ wfun (x + y) := by
          rcases le_total (x + y) (9/4:ℝ) with hq30 | hq30
          · exact le_trans (by norm_num) (wc_161 (x + y) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_182 (x + y) (by linarith) (by linarith))
        have hw4 : (23206737/10000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (17/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_488 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_756 (y + z) (by linarith) (by linarith))
        have hw5 : (1257182497/10000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_962 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_978 (x + y + z) (by linarith) (by linarith))
        linarith
    · have hw2 : (11532825879/10000000000000:ℝ) ≤ wfun z := by
        rcases le_total z (13/4:ℝ) with hq20 | hq20
        · exact le_trans (by norm_num) (wc_388 z (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_390 z (by linarith) (by linarith))
      have hw4 : (5787071159/10000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (17/4:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_753 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_759 (y + z) (by linarith) (by linarith))
      have hw5 : (3116773877/10000000000000:ℝ) ≤ wfun (x + y + z) := by
        rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
        · exact le_trans (by norm_num) (wc_969 (x + y + z) (by linarith) (by linarith))
        rcases le_total (x + y + z) (11/2:ℝ) with hq51 | hq51
        · exact le_trans (by norm_num) (wc_980 (x + y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_982 (x + y + z) (by linarith) (by linarith))
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_5 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (131/128:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (257/128:ℝ) with hc | hc
  · rcases le_total z (131/128:ℝ) with hc | hc
    · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
        rcases le_total x (1:ℝ) with hq00 | hq00
        · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
        rcases le_total y (2:ℝ) with hq10 | hq10
        · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
      have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
        rcases le_total z (1:ℝ) with hq20 | hq20
        · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
      linarith
    · rcases le_total x (257/256:ℝ) with hc | hc
      · have hw0 : (12267823741/5000000000000:ℝ) ≤ wfun x := by
          rcases le_total x (1:ℝ) with hq00 | hq00
          · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_6 x (by linarith) (by linarith))
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
        have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
          rcases le_total (x + y) (3:ℝ) with hq30 | hq30
          · exact le_trans (by norm_num) (wc_198 (x + y) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
        linarith
      · rcases le_total y (509/256:ℝ) with hc | hc
        · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
          have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
          have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
            rcases le_total (x + y) (3:ℝ) with hq30 | hq30
            · exact le_trans (by norm_num) (wc_208 (x + y) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
          linarith
        · rcases le_total z (267/256:ℝ) with hc | hc
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
            have hw5 : (3087/500000000000:ℝ) ≤ wfun (x + y + z) := wc_455 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
            have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
            have hw5 : (159841537/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_512 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (131/128:ℝ) with hc | hc
    · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
        rcases le_total x (1:ℝ) with hq00 | hq00
        · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
      have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
        rcases le_total z (1:ℝ) with hq20 | hq20
        · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
      linarith
    · rcases le_total x (257/256:ℝ) with hc | hc
      · have hw0 : (12267823741/5000000000000:ℝ) ≤ wfun x := by
          rcases le_total x (1:ℝ) with hq00 | hq00
          · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_6 x (by linarith) (by linarith))
        have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
        have hw5 : (59421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_457 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (519/256:ℝ) with hc | hc
        · rcases le_total z (267/256:ℝ) with hc | hc
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
            have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
            have hw5 : (159841537/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_512 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
            have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
            have hw5 : (154654989/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_551 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
          have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
          have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
          have hw5 : (24278963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_552 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_49 (x y z : ℝ) (hx1 : (17/16:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (63/32:ℝ) with hc | hc
  · rcases le_total z (17/16:ℝ) with hc | hc
    · rcases le_total x (141/128:ℝ) with hc | hc
      · rcases le_total y (247/128:ℝ) with hc | hc
        · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
          have hw1 : (9113139537/5000000000000:ℝ) ≤ wfun y := wc_75 y (by linarith) (by linarith)
          have hw4 : (269743281/5000000000000:ℝ) ≤ wfun (y + z) := wc_188 (y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (131/128:ℝ) with hc | hc
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (6731724963/10000000000000:ℝ) ≤ wfun y := wc_78 y (by linarith) (by linarith)
            have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
              rcases le_total z (1:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
            have hw4 : (288828359/5000000000000:ℝ) ≤ wfun (y + z) := wc_189 (y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total y (499/256:ℝ) with hc | hc
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (6028900351/5000000000000:ℝ) ≤ wfun y := wc_77 y (by linarith) (by linarith)
                have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_198 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                have hw5 : (60567/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_456 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (267/256:ℝ) with hc | hc
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1003/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                      have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_208 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_218 (y + z) (by linarith) (by linarith))
                      have hw5 : (81469089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_510 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (529/512:ℝ) with hc | hc
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                        have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                        have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_213 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_218 (y + z) (by linarith) (by linarith))
                        have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_530 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                        have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                        have hw5 : (636617867/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_548 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                    have hw1 : (688065547/1000000000000:ℝ) ≤ wfun y := wc_80 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                    have hw3 : (285997/2500000000000:ℝ) ≤ wfun (x + y) := wc_247 (x + y) (by linarith) (by linarith)
                    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_208 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                    have hw5 : (17805471/500000000000:ℝ) ≤ wfun (x + y + z) := wc_532 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1003/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                      have hw5 : (315273331/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_549 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (539/512:ℝ) with hc | hc
                      · rcases le_total x (1093/1024:ℝ) with hc | hc
                        · have hw0 : (40709377/2000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                          have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                          have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_245 (x + y) (by linarith) (by linarith)
                          have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_586 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (753911279/10000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                          have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                          have hw3 : (28290747/10000000000000:ℝ) ≤ wfun (x + y) := wc_273 (x + y) (by linarith) (by linarith)
                          have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_615 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                        have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                        have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_654 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                    have hw1 : (688065547/1000000000000:ℝ) ≤ wfun y := wc_80 y (by linarith) (by linarith)
                    have hw3 : (285997/2500000000000:ℝ) ≤ wfun (x + y) := wc_247 (x + y) (by linarith) (by linarith)
                    have hw5 : (9646207/100000000000:ℝ) ≤ wfun (x + y + z) := wc_589 (x + y + z) (by linarith) (by linarith)
                    linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (6731724963/10000000000000:ℝ) ≤ wfun y := wc_78 y (by linarith) (by linarith)
              have hw5 : (153865963/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_514 (x + y + z) (by linarith) (by linarith)
              linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
        have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_76 y (by linarith) (by linarith)
        linarith
    · rcases le_total x (141/128:ℝ) with hc | hc
      · rcases le_total y (247/128:ℝ) with hc | hc
        · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
          have hw1 : (9113139537/5000000000000:ℝ) ≤ wfun y := wc_75 y (by linarith) (by linarith)
          have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
          have hw5 : (56143/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_459 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (141/128:ℝ) with hc | hc
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total y (499/256:ℝ) with hc | hc
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (6028900351/5000000000000:ℝ) ≤ wfun y := wc_77 y (by linarith) (by linarith)
                have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw5 : (24278963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_552 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (688065547/1000000000000:ℝ) ≤ wfun y := wc_80 y (by linarith) (by linarith)
                have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw5 : (1335527067/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_658 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (6731724963/10000000000000:ℝ) ≤ wfun y := wc_78 y (by linarith) (by linarith)
              have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw5 : (655310061/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_659 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (6731724963/10000000000000:ℝ) ≤ wfun y := wc_78 y (by linarith) (by linarith)
            have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
            have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
            have hw5 : (2238382569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_741 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
        have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_76 y (by linarith) (by linarith)
        have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
        have hw5 : (271285583/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_556 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total z (17/16:ℝ) with hc | hc
    · rcases le_total x (141/128:ℝ) with hc | hc
      · rcases le_total y (257/128:ℝ) with hc | hc
        · rcases le_total z (131/128:ℝ) with hc | hc
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
            have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
              rcases le_total z (1:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
            have hw3 : (20953831/2500000000000:ℝ) ≤ wfun (x + y) := wc_308 (x + y) (by linarith) (by linarith)
            have hw5 : (58303/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_458 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total y (509/256:ℝ) with hc | hc
              · rcases le_total z (267/256:ℝ) with hc | hc
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1013/512:ℝ) with hc | hc
                    · rcases le_total z (529/512:ℝ) with hc | hc
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                        have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                        have hw5 : (636617867/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_548 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total x (1093/1024:ℝ) with hc | hc
                        · rcases le_total y (2021/1024:ℝ) with hc | hc
                          · have hw0 : (40709377/2000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
                            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                            have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_224 (y + z) (by linarith) (by linarith)
                            have hw5 : (198537007/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_585 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (40709377/2000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
                            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                            have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                            have hw5 : (37329233/312500000000:ℝ) ≤ wfun (x + y + z) := wc_614 (x + y + z) (by linarith) (by linarith)
                            linarith
                        · have hw0 : (753911279/10000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                          have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                          have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
                          have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_615 (x + y + z) (by linarith) (by linarith)
                          linarith
                    · rcases le_total z (529/512:ℝ) with hc | hc
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                        have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                        have hw5 : (49160907/500000000000:ℝ) ≤ wfun (x + y + z) := wc_587 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total x (1093/1024:ℝ) with hc | hc
                        · rcases le_total y (2031/1024:ℝ) with hc | hc
                          · have hw0 : (40709377/2000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                            have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
                            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                            have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                            have hw5 : (1413886087/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_652 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (40709377/2000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
                            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                            have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_692 (x + y + z) (by linarith) (by linarith)
                            linarith
                        · have hw0 : (753911279/10000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                          have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                          have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                          have hw5 : (1642534177/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_693 (x + y + z) (by linarith) (by linarith)
                          linarith
                  · rcases le_total y (1013/512:ℝ) with hc | hc
                    · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                      have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                      have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_588 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                      have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                      have hw5 : (69357131/500000000000:ℝ) ≤ wfun (x + y + z) := wc_655 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1013/512:ℝ) with hc | hc
                    · rcases le_total z (539/512:ℝ) with hc | hc
                      · rcases le_total x (1093/1024:ℝ) with hc | hc
                        · rcases le_total y (2021/1024:ℝ) with hc | hc
                          · have hw0 : (40709377/2000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
                            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                            have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                            have hw5 : (1413886087/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_652 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (40709377/2000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
                            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                            have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                            have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_692 (x + y + z) (by linarith) (by linarith)
                            linarith
                        · have hw0 : (753911279/10000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                          have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                          have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
                          have hw5 : (1642534177/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_693 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                        have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                        have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                        have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_716 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total z (539/512:ℝ) with hc | hc
                      · rcases le_total x (1093/1024:ℝ) with hc | hc
                        · rcases le_total y (2031/1024:ℝ) with hc | hc
                          · have hw0 : (40709377/2000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                            have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
                            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                            have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                            have hw4 : (1166349/10000000000000:ℝ) ≤ wfun (y + z) := wc_245 (y + z) (by linarith) (by linarith)
                            have hw5 : (951861201/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_714 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (40709377/2000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
                            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                            have hw4 : (28290747/10000000000000:ℝ) ≤ wfun (y + z) := wc_273 (y + z) (by linarith) (by linarith)
                            have hw5 : (271686247/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_729 (x + y + z) (by linarith) (by linarith)
                            linarith
                        · have hw0 : (753911279/10000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                          have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                          have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                          have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                          have hw5 : (216315697/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_730 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                        have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                        have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                        have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_736 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                    have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
                    have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                    have hw5 : (1850155147/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_718 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (267/256:ℝ) with hc | hc
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1023/512:ℝ) with hc | hc
                    · rcases le_total z (529/512:ℝ) with hc | hc
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                        have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                        have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_654 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                        have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                        have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                        have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_716 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total z (529/512:ℝ) with hc | hc
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                          rcases le_total y (2:ℝ) with hq10 | hq10
                          · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                        have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                        have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                        have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_716 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                          rcases le_total y (2:ℝ) with hq10 | hq10
                          · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                        have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                        have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                        have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_736 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                    have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_366 (x + y) (by linarith) (by linarith)
                    have hw5 : (1850155147/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_718 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1023/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                      have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_305 (y + z) (by linarith) (by linarith)
                      have hw5 : (2413024171/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_737 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                      have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                      have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                      have hw5 : (3019797449/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_747 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                    have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_366 (x + y) (by linarith) (by linarith)
                    have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                    have hw5 : (2991406031/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_748 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total y (509/256:ℝ) with hc | hc
              · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
                have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                have hw5 : (1335527067/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_658 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
                have hw5 : (1161826227/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_739 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (131/128:ℝ) with hc | hc
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
              rcases le_total z (1:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
            have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw5 : (913271/15625000000:ℝ) ≤ wfun (x + y + z) := wc_554 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total y (519/256:ℝ) with hc | hc
              · rcases le_total z (267/256:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                  have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
                  have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                  have hw5 : (591952751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_738 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                  have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
                  have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                  have hw5 : (1808088631/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_749 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw3 : (1670535297/5000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
                have hw5 : (709810229/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_750 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw3 : (1629257293/5000000000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
              have hw5 : (1741738127/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_751 (x + y + z) (by linarith) (by linarith)
              linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
        have hw3 : (798582451/5000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
        have hw5 : (271285583/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_556 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total x (141/128:ℝ) with hc | hc
      · rcases le_total y (257/128:ℝ) with hc | hc
        · rcases le_total z (141/128:ℝ) with hc | hc
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total y (509/256:ℝ) with hc | hc
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
                have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
                have hw4 : (21491553/2500000000000:ℝ) ≤ wfun (y + z) := wc_307 (y + z) (by linarith) (by linarith)
                have hw5 : (1161826227/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_739 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
                have hw5 : (709810229/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_750 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
              have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (162913869/2500000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
              have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
              have hw5 : (1741738127/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_751 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
            have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
            have hw3 : (20953831/2500000000000:ℝ) ≤ wfun (x + y) := wc_308 (x + y) (by linarith) (by linarith)
            have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (600628743/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_752 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
          have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
          have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
          have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
          have hw5 : (600628743/1250000000000:ℝ) ≤ wfun (x + y + z) := by
            rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
            · exact le_trans (by norm_num) (wc_752 (x + y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_755 (x + y + z) (by linarith) (by linarith))
          linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
        have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
        have hw3 : (798582451/5000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
        have hw4 : (75856633/10000000000000:ℝ) ≤ wfun (y + z) := wc_311 (y + z) (by linarith) (by linarith)
        have hw5 : (600628743/1250000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_752 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_757 (x + y + z) (by linarith) (by linarith))
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_51 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (63/32:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_76 y (by linarith) (by linarith)
  linarith

set_option maxHeartbeats 20000000 in
lemma ch_55 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (257/128:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (267/256:ℝ) with hc | hc
  · rcases le_total y (509/256:ℝ) with hc | hc
    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
      have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
      linarith
    · rcases le_total z (519/256:ℝ) with hc | hc
      · rcases le_total x (529/512:ℝ) with hc | hc
        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
          have hw5 : (14162149/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_770 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (1023/512:ℝ) with hc | hc
          · rcases le_total z (1033/512:ℝ) with hc | hc
            · rcases le_total x (1063/1024:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_245 (x + y) (by linarith) (by linarith)
                have hw5 : (19565737/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_786 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
                  have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
                  have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                  have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (1063/1024:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_245 (x + y) (by linarith) (by linarith)
                have hw5 : (19225319/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_806 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
                  have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_828 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                  have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (1033/512:ℝ) with hc | hc
            · rcases le_total x (1063/1024:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_303 (x + y) (by linarith) (by linarith)
                have hw5 : (19225319/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_806 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                    have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                    have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                    have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                    have hw5 : (134914401/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_826 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                    have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                    have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                    have hw5 : (358152183/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                  have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (1063/1024:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_303 (x + y) (by linarith) (by linarith)
                have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                have hw5 : (71079411/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_844 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                  have hw4 : (32243/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                  have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                  have hw4 : (11791793/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                  have hw5 : (568693187/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_878 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total x (529/512:ℝ) with hc | hc
        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
          have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
          have hw5 : (37716487/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_809 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (1023/512:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
            have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
            have hw4 : (31777/5000000000000:ℝ) ≤ wfun (y + z) := wc_452 (y + z) (by linarith) (by linarith)
            have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
            have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
            have hw4 : (10750333/2500000000000:ℝ) ≤ wfun (y + z) := wc_492 (y + z) (by linarith) (by linarith)
            have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total y (509/256:ℝ) with hc | hc
    · rcases le_total z (519/256:ℝ) with hc | hc
      · rcases le_total x (539/512:ℝ) with hc | hc
        · rcases le_total y (1013/512:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
            have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
            have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
            have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_419 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
            have hw5 : (3568011/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_769 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (1033/512:ℝ) with hc | hc
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · rcases le_total y (2031/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
                  have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                  have hw5 : (314267/40000000000:ℝ) ≤ wfun (x + y + z) := wc_785 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
                  have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                  have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (2031/1024:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
                  have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                  have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
                    have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                    have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                    have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                    have hw5 : (38749297/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_803 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                    have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                    have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                    have hw5 : (134914401/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_826 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_245 (x + y) (by linarith) (by linarith)
                have hw5 : (19225319/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_806 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (2031/1024:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
                  have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
                  have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_828 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                  have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total y (1013/512:ℝ) with hc | hc
          · have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
            have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
            have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
            have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_419 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
            have hw5 : (38680157/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_788 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (1033/512:ℝ) with hc | hc
            · rcases le_total x (1083/1024:ℝ) with hc | hc
              · rcases le_total y (2031/1024:ℝ) with hc | hc
                · have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                  have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                  have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                  have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                  have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_828 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
                have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                have hw5 : (26775111/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_830 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
              have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
              have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (539/512:ℝ) with hc | hc
        · rcases le_total y (1013/512:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
            have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
            have hw5 : (190040129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_808 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
            have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
            have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
            have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (1013/512:ℝ) with hc | hc
          · have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
            have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
            have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
            have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
            have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (519/256:ℝ) with hc | hc
      · rcases le_total x (539/512:ℝ) with hc | hc
        · rcases le_total y (1023/512:ℝ) with hc | hc
          · rcases le_total z (1033/512:ℝ) with hc | hc
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                    have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                    have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                    have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                    have hw5 : (38749297/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_803 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                    have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                    have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                    have hw5 : (134914401/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_826 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · rcases le_total x (2141/2048:ℝ) with hc | hc
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_327 (x + y) (by linarith) (by linarith)
                      have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                      have hw5 : (67587843/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_825 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
                      have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                      have hw5 : (12522987/400000000000:ℝ) ≤ wfun (x + y + z) := wc_835 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (2141/2048:ℝ) with hc | hc
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                      have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_327 (x + y) (by linarith) (by linarith)
                      have hw5 : (71769027/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                      have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
                      have hw5 : (407642947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_853 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · rcases le_total x (2151/2048:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                      have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_327 (x + y) (by linarith) (by linarith)
                      have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                      have hw5 : (67587843/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_825 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                      have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
                      have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                      have hw5 : (12522987/400000000000:ℝ) ≤ wfun (x + y + z) := wc_835 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (2151/2048:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                      have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                      have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_327 (x + y) (by linarith) (by linarith)
                      have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                      have hw5 : (71769027/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                      have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                      have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
                      have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                      have hw5 : (407642947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_853 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · rcases le_total x (2151/2048:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_341 (x + y) (by linarith) (by linarith)
                      have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                      have hw5 : (71769027/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                      have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                      have hw5 : (407642947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_853 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (2151/2048:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                      have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_341 (x + y) (by linarith) (by linarith)
                      have hw5 : (11486191/250000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                      have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                      have hw5 : (257119041/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
                      linarith
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                  have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (2071/1024:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                    have hw2 : (103168503/10000000000000:ℝ) ≤ wfun z := wc_148 z (by linarith) (by linarith)
                    have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                    have hw5 : (458561277/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_150 z (by linarith) (by linarith)
                    have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                    have hw4 : (64801/10000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                    have hw5 : (114178013/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · rcases le_total z (2071/1024:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                    have hw2 : (103168503/10000000000000:ℝ) ≤ wfun z := wc_148 z (by linarith) (by linarith)
                    have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                    have hw5 : (458561277/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_150 z (by linarith) (by linarith)
                    have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                    have hw5 : (114178013/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (2071/1024:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                    have hw2 : (103168503/10000000000000:ℝ) ≤ wfun z := wc_148 z (by linarith) (by linarith)
                    have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                    have hw5 : (114178013/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_150 z (by linarith) (by linarith)
                    have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                    have hw4 : (64801/10000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                    have hw5 : (694962061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_901 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total z (1033/512:ℝ) with hc | hc
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · rcases le_total x (2141/2048:ℝ) with hc | hc
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_341 (x + y) (by linarith) (by linarith)
                      have hw5 : (71769027/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                      have hw5 : (407642947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_853 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (2141/2048:ℝ) with hc | hc
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                      have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_341 (x + y) (by linarith) (by linarith)
                      have hw5 : (11486191/250000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                      have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                      have hw5 : (257119041/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · rcases le_total x (2141/2048:ℝ) with hc | hc
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (493784853/10000000000000:ℝ) ≤ wfun (x + y) := wc_349 (x + y) (by linarith) (by linarith)
                      have hw5 : (11486191/250000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                      have hw5 : (257119041/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                    have hw4 : (64801/10000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                    have hw5 : (114178013/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · rcases le_total x (2151/2048:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (493784853/10000000000000:ℝ) ≤ wfun (x + y) := wc_349 (x + y) (by linarith) (by linarith)
                      have hw5 : (11486191/250000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                      have hw5 : (257119041/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (2151/2048:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                      have hw3 : (493784853/10000000000000:ℝ) ≤ wfun (x + y) := wc_349 (x + y) (by linarith) (by linarith)
                      have hw5 : (571992483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_876 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                      have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                      have hw5 : (316344203/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_895 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                    have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                    have hw5 : (114178013/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                    have hw4 : (64801/10000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                    have hw5 : (694962061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_901 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · rcases le_total z (2071/1024:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                    have hw2 : (103168503/10000000000000:ℝ) ≤ wfun z := wc_148 z (by linarith) (by linarith)
                    have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                    have hw4 : (64801/10000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                    have hw5 : (114178013/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_150 z (by linarith) (by linarith)
                    have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                    have hw4 : (11849221/10000000000000:ℝ) ≤ wfun (y + z) := wc_475 (y + z) (by linarith) (by linarith)
                    have hw5 : (694962061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_901 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                  have hw4 : (11791793/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                  have hw5 : (692290309/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                  have hw4 : (32243/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                  have hw5 : (692290309/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                  have hw4 : (11791793/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                  have hw5 : (827400419/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total y (1023/512:ℝ) with hc | hc
          · rcases le_total z (1033/512:ℝ) with hc | hc
            · rcases le_total x (1083/1024:ℝ) with hc | hc
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                    have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                    have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                    have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                    have hw5 : (358152183/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                    have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                    have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                    have hw5 : (458561277/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (2061/1024:ℝ) with hc | hc
                  · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                    have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                    have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                    have hw5 : (458561277/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                    have hw5 : (114178013/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                  have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                  have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
                  have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                  have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                  have hw5 : (568693187/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_878 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (1083/1024:ℝ) with hc | hc
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                  have hw5 : (568693187/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_878 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                  have hw5 : (692290309/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                have hw5 : (68963139/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (1033/512:ℝ) with hc | hc
            · rcases le_total x (1083/1024:ℝ) with hc | hc
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                  have hw5 : (568693187/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_878 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
                  have hw5 : (692290309/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                have hw5 : (68963139/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
              have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
              have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
              have hw5 : (821066057/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (539/512:ℝ) with hc | hc
        · rcases le_total y (1023/512:ℝ) with hc | hc
          · rcases le_total z (1043/512:ℝ) with hc | hc
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_303 (x + y) (by linarith) (by linarith)
                have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                have hw5 : (566506871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_879 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
                have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                have hw5 : (68963139/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (21355581/2500000000000:ℝ) ≤ wfun z := wc_151 z (by linarith) (by linarith)
              have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
              have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
              have hw5 : (821066057/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (1043/512:ℝ) with hc | hc
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_343 (x + y) (by linarith) (by linarith)
                have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
                have hw5 : (824225629/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
                have hw5 : (194018909/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
              have hw2 : (21355581/2500000000000:ℝ) ≤ wfun z := wc_151 z (by linarith) (by linarith)
              have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
              have hw4 : (8305511/500000000000:ℝ) ≤ wfun (y + z) := wc_507 (y + z) (by linarith) (by linarith)
              have hw5 : (140340159/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (1023/512:ℝ) with hc | hc
          · have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
            have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
            have hw4 : (31777/5000000000000:ℝ) ≤ wfun (y + z) := wc_452 (y + z) (by linarith) (by linarith)
            have hw5 : (814792219/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
            have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
            have hw4 : (10750333/2500000000000:ℝ) ≤ wfun (y + z) := wc_492 (y + z) (by linarith) (by linarith)
            have hw5 : (1114158849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_61 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (179/64:ℝ) ≤ y) (hy2 : y ≤ (747/256:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  have hw1 : (1457053011/2000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
  linarith

end Zeta23Ext.Bridge.FourPoint
