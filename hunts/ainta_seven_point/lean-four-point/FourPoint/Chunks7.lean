import FourPoint.Cells

/-! Chunk module 7 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_1 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (131/64:ℝ) with hc | hc
  · rcases le_total x (17/16:ℝ) with hc | hc
    · rcases le_total y (17/16:ℝ) with hc | hc
      · rcases le_total z (63/32:ℝ) with hc | hc
        · rcases le_total x (131/128:ℝ) with hc | hc
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
              rcases le_total x (1:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
            have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
            linarith
          · rcases le_total y (131/128:ℝ) with hc | hc
            · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
              have hw4 : (269743281/5000000000000:ℝ) ≤ wfun (y + z) := wc_288 (y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (247/128:ℝ) with hc | hc
              · have hw2 : (9113139537/5000000000000:ℝ) ≤ wfun z := wc_116 z (by linarith) (by linarith)
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_257 (x + y) (by linarith) (by linarith)
                have hw4 : (288828359/5000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (267/256:ℝ) with hc | hc
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · rcases le_total z (499/256:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw2 : (6028900351/5000000000000:ℝ) ≤ wfun z := wc_118 z (by linarith) (by linarith)
                      have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
                      have hw4 : (15105971/250000000000:ℝ) ≤ wfun (y + z) := wc_301 (y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw2 : (688065547/1000000000000:ℝ) ≤ wfun z := wc_122 z (by linarith) (by linarith)
                        have hw3 : (115843823/2500000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_312 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw2 : (688065547/1000000000000:ℝ) ≤ wfun z := wc_122 z (by linarith) (by linarith)
                        have hw3 : (1145460727/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_312 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
                        linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                    have hw2 : (6731724963/10000000000000:ℝ) ≤ wfun z := wc_119 z (by linarith) (by linarith)
                    have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw2 : (6731724963/10000000000000:ℝ) ≤ wfun z := wc_119 z (by linarith) (by linarith)
                    have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_302 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
                    linarith
                  · have hw2 : (6731724963/10000000000000:ℝ) ≤ wfun z := wc_119 z (by linarith) (by linarith)
                    have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
                    have hw5 : (60567/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_705 (x + y + z) (by linarith) (by linarith)
                    linarith
        · rcases le_total x (131/128:ℝ) with hc | hc
          · rcases le_total y (131/128:ℝ) with hc | hc
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              linarith
            · rcases le_total z (257/128:ℝ) with hc | hc
              · rcases le_total x (257/256:ℝ) with hc | hc
                · have hw0 : (12267823741/5000000000000:ℝ) ≤ wfun x := by
                    rcases le_total x (1:ℝ) with hq00 | hq00
                    · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_6 x (by linarith) (by linarith))
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  linarith
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                    linarith
                  · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
                    have hw5 : (60567/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_705 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (257/256:ℝ) with hc | hc
                · have hw0 : (12267823741/5000000000000:ℝ) ≤ wfun x := by
                    rcases le_total x (1:ℝ) with hq00 | hq00
                    · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_6 x (by linarith) (by linarith))
                  have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_489 (y + z) (by linarith) (by linarith)
                  have hw5 : (59421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw4 : (21491553/2500000000000:ℝ) ≤ wfun (y + z) := wc_488 (y + z) (by linarith) (by linarith)
                    have hw5 : (39204539/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_787 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
                    have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_576 (y + z) (by linarith) (by linarith)
                    have hw5 : (24278963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_830 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total y (131/128:ℝ) with hc | hc
            · rcases le_total z (257/128:ℝ) with hc | hc
              · rcases le_total x (267/256:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (1:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  linarith
                · rcases le_total y (257/256:ℝ) with hc | hc
                  · have hw1 : (12267823741/5000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (1:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_6 y (by linarith) (by linarith))
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_302 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
                    linarith
                  · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := wc_9 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
                    have hw5 : (60567/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_705 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (267/256:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (1:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                  have hw5 : (59421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (257/256:ℝ) with hc | hc
                  · have hw1 : (12267823741/5000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (1:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_6 y (by linarith) (by linarith))
                    have hw5 : (39204539/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_787 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := wc_9 y (by linarith) (by linarith)
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
                    have hw5 : (24278963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_830 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (257/128:ℝ) with hc | hc
              · rcases le_total x (267/256:ℝ) with hc | hc
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · rcases le_total z (509/256:ℝ) with hc | hc
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                          have hw3 : (94460693/2000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                          have hw5 : (31471/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                          have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                          have hw5 : (1064707/250000000000:ℝ) ≤ wfun (x + y + z) := wc_760 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                          have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                          have hw5 : (1064707/250000000000:ℝ) ≤ wfun (x + y + z) := wc_760 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · rcases le_total z (1013/512:ℝ) with hc | hc
                          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                            have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                            have hw2 : (4884069333/10000000000000:ℝ) ≤ wfun z := wc_132 z (by linarith) (by linarith)
                            have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                            have hw5 : (164514637/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_783 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                            have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                            have hw2 : (3192232409/10000000000000:ℝ) ≤ wfun z := wc_165 z (by linarith) (by linarith)
                            have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                            have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                            linarith
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                          have hw3 : (94460693/2000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                          have hw5 : (81469089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_784 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · rcases le_total z (1023/512:ℝ) with hc | hc
                          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                            have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                            have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                            have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                            have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                            have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                            have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                              rcases le_total z (2:ℝ) with hq20 | hq20
                              · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                              exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                            have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                            have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                            have hw5 : (636617867/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_826 (x + y + z) (by linarith) (by linarith)
                            linarith
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · rcases le_total z (1023/512:ℝ) with hc | hc
                          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                            have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                            have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                            have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                            have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                            have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                              rcases le_total z (2:ℝ) with hq20 | hq20
                              · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                              exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                            have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                            have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                            have hw5 : (636617867/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_826 (x + y + z) (by linarith) (by linarith)
                            linarith
                        · rcases le_total z (1023/512:ℝ) with hc | hc
                          · rcases le_total x (1063/1024:ℝ) with hc | hc
                            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                              have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                              have hw3 : (54451693/250000000000:ℝ) ≤ wfun (x + y) := wc_263 (x + y) (by linarith) (by linarith)
                              have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                              have hw5 : (79960111/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_825 (x + y + z) (by linarith) (by linarith)
                              linarith
                            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                              have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                              have hw3 : (1392763463/5000000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                              have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                              have hw5 : (402392913/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_852 (x + y + z) (by linarith) (by linarith)
                              linarith
                          · rcases le_total x (1063/1024:ℝ) with hc | hc
                            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
                              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                                rcases le_total z (2:ℝ) with hq20 | hq20
                                · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                                exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                              have hw3 : (54451693/250000000000:ℝ) ≤ wfun (x + y) := wc_263 (x + y) (by linarith) (by linarith)
                              have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                              have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_879 (x + y + z) (by linarith) (by linarith)
                              linarith
                            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                                rcases le_total z (2:ℝ) with hq20 | hq20
                                · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                                exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                              have hw3 : (1392763463/5000000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                              have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                              have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_931 (x + y + z) (by linarith) (by linarith)
                              linarith
                  · rcases le_total z (509/256:ℝ) with hc | hc
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                        have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                        have hw3 : (264638553/1250000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                        have hw5 : (20172571/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_785 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                        have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                        have hw3 : (3366163659/10000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                        have hw5 : (17805471/500000000000:ℝ) ≤ wfun (x + y + z) := wc_807 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                        have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                          rcases le_total z (2:ℝ) with hq20 | hq20
                          · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                        have hw3 : (264638553/1250000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                        have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_487 (y + z) (by linarith) (by linarith)
                        have hw5 : (624547701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_828 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                        have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                          rcases le_total z (2:ℝ) with hq20 | hq20
                          · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                        have hw3 : (3366163659/10000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                        have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_487 (y + z) (by linarith) (by linarith)
                        have hw5 : (9646207/100000000000:ℝ) ≤ wfun (x + y + z) := wc_882 (x + y + z) (by linarith) (by linarith)
                        linarith
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · rcases le_total z (509/256:ℝ) with hc | hc
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                          have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                          have hw5 : (81469089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_784 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                          have hw3 : (343008739/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
                          have hw5 : (89884553/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_806 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                        have hw3 : (3366163659/10000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                        have hw5 : (17805471/500000000000:ℝ) ≤ wfun (x + y + z) := wc_807 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                          have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                          have hw5 : (315273331/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_827 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                          have hw3 : (343008739/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
                          have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                          have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                          have hw3 : (343008739/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
                          have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                          have hw3 : (2485973639/5000000000000:ℝ) ≤ wfun (x + y) := wc_271 (x + y) (by linarith) (by linarith)
                          have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                          have hw5 : (69357131/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1021 (x + y + z) (by linarith) (by linarith)
                          linarith
                  · rcases le_total z (509/256:ℝ) with hc | hc
                    · have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                      have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
                      have hw5 : (154654989/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_829 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
                      have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_487 (y + z) (by linarith) (by linarith)
                      have hw5 : (1361028853/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1023 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total x (267/256:ℝ) with hc | hc
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · rcases le_total z (519/256:ℝ) with hc | hc
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                          have hw3 : (94460693/2000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                          have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_486 (y + z) (by linarith) (by linarith)
                          have hw5 : (315273331/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_827 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                          have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                          have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_557 (y + z) (by linarith) (by linarith)
                          have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                          have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
                          have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_486 (y + z) (by linarith) (by linarith)
                          have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                          have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                          have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_557 (y + z) (by linarith) (by linarith)
                          have hw5 : (69357131/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1021 (x + y + z) (by linarith) (by linarith)
                          linarith
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw3 : (115843823/2500000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                        have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                        have hw5 : (274801629/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1022 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw3 : (1145460727/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                        have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                        have hw5 : (1850155147/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1156 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total z (519/256:ℝ) with hc | hc
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                        have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                        have hw3 : (264638553/1250000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
                        have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                        have hw5 : (274801629/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1022 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
                        have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                        have hw3 : (3366163659/10000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                        have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                        have hw5 : (1850155147/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1156 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                      have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                      have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_590 (y + z) (by linarith) (by linarith)
                      have hw5 : (591952751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1184 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · rcases le_total z (519/256:ℝ) with hc | hc
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                          have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                          have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_486 (y + z) (by linarith) (by linarith)
                          have hw5 : (69357131/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1021 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                          have hw3 : (343008739/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
                          have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_557 (y + z) (by linarith) (by linarith)
                          have hw5 : (933899467/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1155 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                        have hw3 : (3366163659/10000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                        have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_487 (y + z) (by linarith) (by linarith)
                        have hw5 : (1850155147/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1156 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                      have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
                      have hw5 : (591952751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1184 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
                    have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_576 (y + z) (by linarith) (by linarith)
                    have hw5 : (1161826227/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1185 (x + y + z) (by linarith) (by linarith)
                    linarith
      · rcases le_total z (63/32:ℝ) with hc | hc
        · rcases le_total x (131/128:ℝ) with hc | hc
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
              rcases le_total x (1:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
            have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
            have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
            have hw3 : (12244337/312500000000:ℝ) ≤ wfun (x + y) := wc_258 (x + y) (by linarith) (by linarith)
            linarith
          · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
            have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
            have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
            linarith
        · rcases le_total x (131/128:ℝ) with hc | hc
          · rcases le_total y (141/128:ℝ) with hc | hc
            · rcases le_total z (257/128:ℝ) with hc | hc
              · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                  rcases le_total x (1:ℝ) with hq00 | hq00
                  · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
                have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_257 (x + y) (by linarith) (by linarith)
                have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_489 (y + z) (by linarith) (by linarith)
                have hw5 : (58303/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_707 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                  rcases le_total x (1:ℝ) with hq00 | hq00
                  · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
                have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_257 (x + y) (by linarith) (by linarith)
                have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
                have hw5 : (913271/15625000000:ℝ) ≤ wfun (x + y + z) := wc_832 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw1 : (11778340313/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
              have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_594 (y + z) (by linarith) (by linarith)
              have hw5 : (563044583/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_833 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (141/128:ℝ) with hc | hc
            · rcases le_total z (257/128:ℝ) with hc | hc
              · rcases le_total x (267/256:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (4615617497/10000000000000:ℝ) ≤ wfun (x + y) := wc_273 (x + y) (by linarith) (by linarith)
                  have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_489 (y + z) (by linarith) (by linarith)
                  have hw5 : (297800559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_831 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (2045420557/2500000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                  have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_489 (y + z) (by linarith) (by linarith)
                  have hw5 : (655310061/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1025 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
                have hw5 : (2238382569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1187 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (11778340313/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw3 : (48584483/40000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_594 (y + z) (by linarith) (by linarith)
              have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1188 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (17/16:ℝ) with hc | hc
      · rcases le_total z (63/32:ℝ) with hc | hc
        · rcases le_total x (141/128:ℝ) with hc | hc
          · rcases le_total y (131/128:ℝ) with hc | hc
            · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
              have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
              have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_257 (x + y) (by linarith) (by linarith)
              have hw4 : (269743281/5000000000000:ℝ) ≤ wfun (y + z) := wc_288 (y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
              have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
              have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
              linarith
          · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_108 x (by linarith) (by linarith)
            have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
            have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
            linarith
        · rcases le_total x (141/128:ℝ) with hc | hc
          · rcases le_total y (131/128:ℝ) with hc | hc
            · rcases le_total z (257/128:ℝ) with hc | hc
              · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
                have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_257 (x + y) (by linarith) (by linarith)
                have hw5 : (58303/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_707 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
                have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_257 (x + y) (by linarith) (by linarith)
                have hw5 : (913271/15625000000:ℝ) ≤ wfun (x + y + z) := wc_832 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (257/128:ℝ) with hc | hc
              · rcases le_total x (277/256:ℝ) with hc | hc
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                    have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
                    have hw5 : (24278963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_830 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                    have hw3 : (4243616393/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                    have hw5 : (1335527067/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1024 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_107 x (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_134 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (2045420557/2500000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                  have hw5 : (655310061/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1025 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
                have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_489 (y + z) (by linarith) (by linarith)
                have hw5 : (2238382569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1187 (x + y + z) (by linarith) (by linarith)
                linarith
          · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_108 x (by linarith) (by linarith)
            have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
            have hw5 : (271285583/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_834 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_104 x (by linarith) (by linarith)
        have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
        have hw3 : (2788858101/2500000000000:ℝ) ≤ wfun (x + y) := by
          rcases le_total (x + y) (9/4:ℝ) with hq30 | hq30
          · exact le_trans (by norm_num) (wc_279 (x + y) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_282 (x + y) (by linarith) (by linarith))
        have hw5 : (13029/2500000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_709 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_1204 (x + y + z) (by linarith) (by linarith))
        linarith
  · rcases le_total x (17/16:ℝ) with hc | hc
    · rcases le_total y (17/16:ℝ) with hc | hc
      · rcases le_total z (17/8:ℝ) with hc | hc
        · rcases le_total x (131/128:ℝ) with hc | hc
          · rcases le_total y (131/128:ℝ) with hc | hc
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_257 z (by linarith) (by linarith)
              have hw4 : (79711817/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
              have hw5 : (56143/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_708 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_257 z (by linarith) (by linarith)
              have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_594 (y + z) (by linarith) (by linarith)
              have hw5 : (563044583/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_833 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (131/128:ℝ) with hc | hc
            · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_257 z (by linarith) (by linarith)
              have hw4 : (79711817/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
              have hw5 : (563044583/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_833 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (267/128:ℝ) with hc | hc
              · rcases le_total x (267/256:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw2 : (18186303/400000000000:ℝ) ≤ wfun z := wc_255 z (by linarith) (by linarith)
                  have hw3 : (437829947/10000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                  have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
                  have hw5 : (18244153/80000000000:ℝ) ≤ wfun (x + y + z) := wc_1186 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw2 : (18186303/400000000000:ℝ) ≤ wfun z := wc_255 z (by linarith) (by linarith)
                  have hw3 : (2001469121/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                  have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_592 (y + z) (by linarith) (by linarith)
                  have hw5 : (1741738127/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1198 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw2 : (4789633321/10000000000000:ℝ) ≤ wfun z := wc_272 z (by linarith) (by linarith)
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_257 (x + y) (by linarith) (by linarith)
                have hw4 : (5096134953/10000000000000:ℝ) ≤ wfun (y + z) := wc_604 (y + z) (by linarith) (by linarith)
                have hw5 : (600628743/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1199 (x + y + z) (by linarith) (by linarith)
                linarith
        · have hw2 : (48584483/40000000000:ℝ) ≤ wfun z := wc_278 z (by linarith) (by linarith)
          have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_606 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_609 (y + z) (by linarith) (by linarith))
          have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := by
            rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
            · exact le_trans (by norm_num) (wc_1188 (x + y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_1204 (x + y + z) (by linarith) (by linarith))
          linarith
      · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
        have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_259 z (by linarith) (by linarith)
        have hw3 : (182240171/5000000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
        have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_606 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_612 (y + z) (by linarith) (by linarith))
        have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_1188 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_1205 (x + y + z) (by linarith) (by linarith))
        linarith
    · rcases le_total y (17/16:ℝ) with hc | hc
      · rcases le_total z (17/8:ℝ) with hc | hc
        · rcases le_total x (141/128:ℝ) with hc | hc
          · rcases le_total y (131/128:ℝ) with hc | hc
            · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
              have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_257 z (by linarith) (by linarith)
              have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_257 (x + y) (by linarith) (by linarith)
              have hw4 : (79711817/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
              have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1188 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
              have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_257 z (by linarith) (by linarith)
              have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
              have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_594 (y + z) (by linarith) (by linarith)
              have hw5 : (600628743/1250000000000:ℝ) ≤ wfun (x + y + z) := by
                rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
                · exact le_trans (by norm_num) (wc_1199 (x + y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_1202 (x + y + z) (by linarith) (by linarith))
              linarith
          · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_108 x (by linarith) (by linarith)
            have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_257 z (by linarith) (by linarith)
            have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
            have hw4 : (75856633/10000000000000:ℝ) ≤ wfun (y + z) := wc_492 (y + z) (by linarith) (by linarith)
            have hw5 : (600628743/1250000000000:ℝ) ≤ wfun (x + y + z) := by
              rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
              · exact le_trans (by norm_num) (wc_1199 (x + y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_1204 (x + y + z) (by linarith) (by linarith))
            linarith
        · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_104 x (by linarith) (by linarith)
          have hw2 : (48584483/40000000000:ℝ) ≤ wfun z := wc_278 z (by linarith) (by linarith)
          have hw3 : (182240171/5000000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
          have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_606 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_609 (y + z) (by linarith) (by linarith))
          have hw5 : (8382305677/10000000000000:ℝ) ≤ wfun (x + y + z) := by
            rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
            · exact le_trans (by norm_num) (wc_1201 (x + y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_1205 (x + y + z) (by linarith) (by linarith))
          linarith
      · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_104 x (by linarith) (by linarith)
        have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
        have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_259 z (by linarith) (by linarith)
        have hw3 : (2788858101/2500000000000:ℝ) ≤ wfun (x + y) := by
          rcases le_total (x + y) (9/4:ℝ) with hq30 | hq30
          · exact le_trans (by norm_num) (wc_279 (x + y) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_282 (x + y) (by linarith) (by linarith))
        have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_606 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_612 (y + z) (by linarith) (by linarith))
        have hw5 : (8382305677/10000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_1201 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_1207 (x + y + z) (by linarith) (by linarith))
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_17 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (1063/1024:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (2021/1024:ℝ) with hc | hc
  · rcases le_total z (1073/1024:ℝ) with hc | hc
    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
      have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
      have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
      have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_802 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total x (2121/2048:ℝ) with hc | hc
      · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
        have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
        have hw3 : (93531111/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
        have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_812 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
        have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
        have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_332 (x + y) (by linarith) (by linarith)
        have hw5 : (570814473/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_818 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total z (1073/1024:ℝ) with hc | hc
    · rcases le_total x (2121/2048:ℝ) with hc | hc
      · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
        have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
        have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
        have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_812 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (4047/2048:ℝ) with hc | hc
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
          have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
          have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_336 (x + y) (by linarith) (by linarith)
          have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_817 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
            have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
            have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (2121/2048:ℝ) with hc | hc
      · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
        have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
        have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
        have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
        have hw5 : (323709737/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_822 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (4047/2048:ℝ) with hc | hc
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
          have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_336 (x + y) (by linarith) (by linarith)
          have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_362 (y + z) (by linarith) (by linarith)
          have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
            have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
            have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
            have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
            have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_25 (x y z : ℝ) (hx1 : (1063/1024:ℝ) ≤ x) (hx2 : x ≤ (2131/2048:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (4067/2048:ℝ) with hc | hc
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4257/4096:ℝ) with hc | hc
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
          have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
          have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
          have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
          have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_872 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
            have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
            have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
            have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
            have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
            have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8519/8192:ℝ) with hc | hc
            · have hw0 : (482068367/2000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_908 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_916 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (4257/4096:ℝ) with hc | hc
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
            have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
            have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
            have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
            have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
            have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8519/8192:ℝ) with hc | hc
            · have hw0 : (482068367/2000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_908 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
              have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_916 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8519/8192:ℝ) with hc | hc
            · have hw0 : (482068367/2000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
              have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
              have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8519/8192:ℝ) with hc | hc
            · have hw0 : (482068367/2000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
              have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
              have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8519/8192:ℝ) with hc | hc
            · have hw0 : (482068367/2000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
              have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
              have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4257/4096:ℝ) with hc | hc
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
            have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
            have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
            have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
            have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
            have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
            have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
            have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8519/8192:ℝ) with hc | hc
            · have hw0 : (482068367/2000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
              have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
              have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
            have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
            have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
            have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (4257/4096:ℝ) with hc | hc
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
            have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
            have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
            have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
            have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
            have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
            have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
            have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
            have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8519/8192:ℝ) with hc | hc
            · have hw0 : (482068367/2000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
              have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
              have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8519/8192:ℝ) with hc | hc
            · have hw0 : (482068367/2000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
              have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
              have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_980 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
            have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
            have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
            have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
            have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_35 (x y z : ℝ) (hx1 : (1063/1024:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (2041/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (1073/1024:ℝ) with hc | hc
  · rcases le_total x (2131/2048:ℝ) with hc | hc
    · rcases le_total y (4077/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
              have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
              have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_507 (y + z) (by linarith) (by linarith)
              have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
              have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · rcases le_total y (8159/4096:ℝ) with hc | hc
            · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
              have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
              have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
              have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8159/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · rcases le_total y (8159/4096:ℝ) with hc | hc
            · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
              have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
              have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
              have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8159/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
              have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
              have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (4077/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · rcases le_total x (8529/8192:ℝ) with hc | hc
                · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                  have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                  have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                  have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                  have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_980 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8529/8192:ℝ) with hc | hc
                · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                  have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                  have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1001 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (8529/8192:ℝ) with hc | hc
                · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                  have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1010 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · rcases le_total x (8539/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                  have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                  have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (16293/8192:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                    have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                    have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                    have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                    have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (8539/8192:ℝ) with hc | hc
                · rcases le_total y (16293/8192:ℝ) with hc | hc
                  · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                    have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                    have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                    have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                    have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                    have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                    have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (16293/8192:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                    have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                    have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                    have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                    have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · rcases le_total x (8539/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                  have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                  have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1010 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                  have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8539/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                  have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                  have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8529/8192:ℝ) with hc | hc
                · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                  have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1010 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8529/8192:ℝ) with hc | hc
                · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8529/8192:ℝ) with hc | hc
                · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8539/8192:ℝ) with hc | hc
                · rcases le_total y (16293/8192:ℝ) with hc | hc
                  · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                    have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                    have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                    have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                    have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                    have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                    have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (16293/8192:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                    have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                    have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                    have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                    have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (8539/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (16293/8192:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                    have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                    have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                    have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                    have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                    have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · rcases le_total x (8539/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (8539/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                  have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                  have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8159/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8159/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (8539/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_505 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_511 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8159/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8159/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
                have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total x (2131/2048:ℝ) with hc | hc
    · rcases le_total y (4077/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
              have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
              have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
              have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
              have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
              have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_418 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
            have hw5 : (775154287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1067 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_436 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
            have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1088 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_450 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
            have hw5 : (775154287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1067 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8159/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
              have hw4 : (10193319/400000000000:ℝ) ≤ wfun (y + z) := wc_543 (y + z) (by linarith) (by linarith)
              have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1087 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
              have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
              have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1103 (x + y + z) (by linarith) (by linarith)
              linarith
        · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
          have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
          have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
          have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
          have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1105 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (4077/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · rcases le_total x (8539/8192:ℝ) with hc | hc
                · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                  have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                  have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
                have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
              have hw4 : (10193319/400000000000:ℝ) ≤ wfun (y + z) := wc_543 (y + z) (by linarith) (by linarith)
              have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1103 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
              have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
              have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8149/4096:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
              have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
              have hw4 : (10193319/400000000000:ℝ) ≤ wfun (y + z) := wc_543 (y + z) (by linarith) (by linarith)
              have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
              have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
              have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8159/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
              have hw4 : (10193319/400000000000:ℝ) ≤ wfun (y + z) := wc_543 (y + z) (by linarith) (by linarith)
              have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1103 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
              have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
              have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8159/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
                have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
                have hw4 : (290088193/10000000000000:ℝ) ≤ wfun (y + z) := wc_548 (y + z) (by linarith) (by linarith)
                have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
              have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
              have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
              have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (5774823/625000000000:ℝ) ≤ wfun (x + y) := wc_480 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (1798491653/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1132 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_507 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1142 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_70 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (2021/1024:ℝ) ≤ y) (hy2 : y ≤ (4047/2048:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (2141/2048:ℝ) with hc | hc
  · rcases le_total x (4297/4096:ℝ) with hc | hc
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
          have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
          have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (268673/10000000000000:ℝ) ≤ wfun (y + z) := wc_349 (y + z) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (268673/10000000000000:ℝ) ≤ wfun (y + z) := wc_349 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (268673/10000000000000:ℝ) ≤ wfun (y + z) := wc_349 (y + z) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (268673/10000000000000:ℝ) ≤ wfun (y + z) := wc_349 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
          have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
          have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
            have hw5 : (554620627/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_895 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
            have hw5 : (1135024061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_904 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
            have hw5 : (554620627/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_895 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
            have hw5 : (1135024061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_904 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (4297/4096:ℝ) with hc | hc
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
              have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
              have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_71 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (4047/2048:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (2141/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4297/4096:ℝ) with hc | hc
  · rcases le_total y (8099/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
            have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
            have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17173/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17183/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total y (8099/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
            have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
              have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
            have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
              have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17193/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_77 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (4047/2048:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (2151/2048:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4297/4096:ℝ) with hc | hc
  · rcases le_total y (8099/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
            have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
            have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
            have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
            have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
            have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
            have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
            have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
          have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
          have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
          have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
            have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
            have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
            have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
            have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
            have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total y (8099/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
            have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
            have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
            have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
            have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
          have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
          have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
          have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
          have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
          have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
          have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
            have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
            have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
            have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
            have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
          have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_416 (x + y) (by linarith) (by linarith)
          have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
          have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
          have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_428 (x + y) (by linarith) (by linarith)
          have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
          have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_79 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (539/512:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1073/1024:ℝ) with hc | hc
  · rcases le_total y (2021/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · rcases le_total y (4037/2048:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
            have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_362 (y + z) (by linarith) (by linarith)
            have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_875 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4277/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_898 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (8079/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
                  have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
                  have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_910 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
                  have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                  have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
              have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (4037/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_898 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (1157601093/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_911 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
              have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · rcases le_total y (8079/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
                  have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
                  have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                  have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8079/4096:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
                  have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                  have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
              have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
          have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
          have hw5 : (1203159081/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_928 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
          have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
          have hw5 : (655719053/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_971 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4277/4096:ℝ) with hc | hc
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
                  have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                  have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_924 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                  have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                  have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                  have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
              have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4277/4096:ℝ) with hc | hc
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                  have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_466 (y + z) (by linarith) (by linarith)
                  have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                  have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                    have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                    have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                    have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                    have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (4277/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1013 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1046 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                  have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                  have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                  have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                    have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                    have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
                    have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                    have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                    have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                    have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1013 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1046 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                    have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                    have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                    have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                    have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · rcases le_total x (8569/8192:ℝ) with hc | hc
                    · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                      have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                      have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
                      have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                      have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                      have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                      have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
                      have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                      have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                    have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                    have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                    have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                    have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1044 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                    have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                    have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · rcases le_total x (8579/8192:ℝ) with hc | hc
                    · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                      have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                      have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
                      have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                      have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                      have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                      have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
                      have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                      have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                    have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                    have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (4287/4096:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                have hw5 : (775154287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1067 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_375 (x + y) (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1088 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
            have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_482 (y + z) (by linarith) (by linarith)
            have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1015 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_518 (y + z) (by linarith) (by linarith)
            have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1069 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
            have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_482 (y + z) (by linarith) (by linarith)
            have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1069 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
            have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_518 (y + z) (by linarith) (by linarith)
            have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1106 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total y (2021/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2151/2048:ℝ) with hc | hc
        · rcases le_total y (4037/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4297/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_925 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_361 (y + z) (by linarith) (by linarith)
                have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_948 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
              have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
              have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
              have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_969 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4297/4096:ℝ) with hc | hc
              · rcases le_total y (8079/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
                  have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_967 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                  have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8079/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                  have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_388 (y + z) (by linarith) (by linarith)
                  have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_991 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_404 (y + z) (by linarith) (by linarith)
                  have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
              have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1014 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (4037/2048:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_362 (y + z) (by linarith) (by linarith)
            have hw5 : (262917659/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_970 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4307/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1013 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_375 (x + y) (by linarith) (by linarith)
                have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_389 (y + z) (by linarith) (by linarith)
                have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1046 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
              have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
              have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1068 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (2151/2048:ℝ) with hc | hc
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
          have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
          have hw5 : (1424080951/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1016 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
          have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
          have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1070 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2151/2048:ℝ) with hc | hc
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4297/4096:ℝ) with hc | hc
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                  have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1012 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                  have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                  have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1045 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                  have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
              have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
              have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1068 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4297/4096:ℝ) with hc | hc
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                    have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                    have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1065 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                    have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                    have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (4317/4096:ℝ) with hc | hc
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (85656967/10000000000000:ℝ) ≤ wfun z := wc_92 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
                    have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_95 z (by linarith) (by linarith)
                    have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                    have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                    have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                  have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1087 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                  have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_466 (y + z) (by linarith) (by linarith)
                  have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1103 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (4297/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_388 (x + y) (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                have hw5 : (418067961/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1104 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
                have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_404 (x + y) (by linarith) (by linarith)
                have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1123 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4307/4096:ℝ) with hc | hc
              · rcases le_total y (8089/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                  have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1066 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_436 (y + z) (by linarith) (by linarith)
                  have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1087 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_404 (x + y) (by linarith) (by linarith)
                have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_419 (y + z) (by linarith) (by linarith)
                have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1088 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
              have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
              have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1105 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4307/4096:ℝ) with hc | hc
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                  have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                  have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1103 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_466 (y + z) (by linarith) (by linarith)
                  have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (8099/4096:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                  have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1122 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_466 (y + z) (by linarith) (by linarith)
                  have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1131 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
              have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
              have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
              have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
              have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1133 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (2151/2048:ℝ) with hc | hc
        · rcases le_total y (4047/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
            have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_482 (y + z) (by linarith) (by linarith)
            have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1106 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
            have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_518 (y + z) (by linarith) (by linarith)
            have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1134 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
          have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
          have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
          have hw3 : (5174037/5000000000000:ℝ) ≤ wfun (x + y) := wc_390 (x + y) (by linarith) (by linarith)
          have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
          have hw5 : (1787757479/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1135 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_124 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (4067/2048:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (2141/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4277/4096:ℝ) with hc | hc
  · rcases le_total y (8139/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
            have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
            have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (8139/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_145 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (4297/4096:ℝ))
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
  · rcases le_total x (8589/8192:ℝ) with hc | hc
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17133/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17143/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (8589/8192:ℝ) with hc | hc
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · rcases le_total z (17163/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (186246483/2500000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17153/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17173/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16233/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32461/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17183/16384:ℝ) with hc | hc
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32471/16384:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_154 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (2151/2048:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4297/4096:ℝ) with hc | hc
  · rcases le_total y (8119/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
            have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
            have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
            have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
            have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
          have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
          have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
          have hw5 : (43501511/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1120 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
          have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
          have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
          have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8589/8192:ℝ) with hc | hc
        · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
          have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
          have hw5 : (180388897/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1129 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_472 (x + y) (by linarith) (by linarith)
          have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
          have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total y (8119/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
            have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
            have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
            have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
            have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
            have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
            have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
            have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
            have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
        have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
        have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_465 (x + y) (by linarith) (by linarith)
        have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
        have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8599/8192:ℝ) with hc | hc
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (183730059/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1136 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
          have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
          have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
          have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
        have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
        have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
        have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
        have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_166 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (1023/512:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (529/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1073/1024:ℝ) with hc | hc
  · rcases le_total y (2041/1024:ℝ) with hc | hc
    · rcases le_total z (1053/1024:ℝ) with hc | hc
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
        have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
        have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
        have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
        have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_823 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
          have hw3 : (22987523/2500000000000:ℝ) ≤ wfun (x + y) := wc_482 (x + y) (by linarith) (by linarith)
          have hw5 : (407254991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_849 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
          have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
          have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_518 (x + y) (by linarith) (by linarith)
          have hw5 : (45246083/500000000000:ℝ) ≤ wfun (x + y + z) := wc_862 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (1053/1024:ℝ) with hc | hc
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
        have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
        have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
        have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
        have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_850 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
          have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_532 (x + y) (by linarith) (by linarith)
          have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
          have hw5 : (199972023/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_876 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
          have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_545 (x + y) (by linarith) (by linarith)
          have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
          have hw5 : (549643007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_901 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total y (2041/1024:ℝ) with hc | hc
    · rcases le_total z (1053/1024:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
        have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
        have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
        have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
        have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_850 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
        have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
        have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
        have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (1053/1024:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
        have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
        have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
        have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
        have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
        have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
        have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
        have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
        have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_929 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_214 (x y z : ℝ) (hx1 : (257/128:ℝ) ≤ x) (hx2 : x ≤ (131/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (17/16:ℝ))
    (hz1 : (63/32:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (131/128:ℝ) with hc | hc
  · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
      rcases le_total y (1:ℝ) with hq10 | hq10
      · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
    linarith
  · rcases le_total z (257/128:ℝ) with hc | hc
    · rcases le_total x (519/256:ℝ) with hc | hc
      · rcases le_total y (267/256:ℝ) with hc | hc
        · rcases le_total z (509/256:ℝ) with hc | hc
          · rcases le_total x (1033/512:ℝ) with hc | hc
            · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
              have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
              have hw3 : (22330933/2500000000000:ℝ) ≤ wfun (x + y) := wc_486 (x + y) (by linarith) (by linarith)
              linarith
            · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
              have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
              have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_557 (x + y) (by linarith) (by linarith)
              linarith
          · rcases le_total x (1033/512:ℝ) with hc | hc
            · rcases le_total y (529/512:ℝ) with hc | hc
              · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
                have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
                have hw5 : (3568011/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1220 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (1023/512:ℝ) with hc | hc
                · rcases le_total x (2061/1024:ℝ) with hc | hc
                  · rcases le_total y (1063/1024:ℝ) with hc | hc
                    · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_242 x (by linarith) (by linarith)
                      have hw1 : (2957142633/10000000000000:ℝ) ≤ wfun y := wc_18 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                      have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
                      have hw4 : (1166349/10000000000000:ℝ) ≤ wfun (y + z) := wc_364 (y + z) (by linarith) (by linarith)
                      have hw5 : (314267/40000000000:ℝ) ≤ wfun (x + y + z) := wc_1238 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_242 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_25 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                      have hw4 : (28290747/10000000000000:ℝ) ≤ wfun (y + z) := wc_422 (y + z) (by linarith) (by linarith)
                      have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1249 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_246 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                    have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                    have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_565 (x + y) (by linarith) (by linarith)
                    have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                    have hw5 : (129046413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1250 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (2061/1024:ℝ) with hc | hc
                  · rcases le_total y (1063/1024:ℝ) with hc | hc
                    · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_242 x (by linarith) (by linarith)
                      have hw1 : (2957142633/10000000000000:ℝ) ≤ wfun y := wc_18 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
                      have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_484 (y + z) (by linarith) (by linarith)
                      have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1264 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_242 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_25 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                      have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_534 (y + z) (by linarith) (by linarith)
                      have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1290 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (1063/1024:ℝ) with hc | hc
                    · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_246 x (by linarith) (by linarith)
                      have hw1 : (2957142633/10000000000000:ℝ) ≤ wfun y := wc_18 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                      have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_484 (y + z) (by linarith) (by linarith)
                      have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1290 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_246 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_25 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                      have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_534 (y + z) (by linarith) (by linarith)
                      have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1312 (x + y + z) (by linarith) (by linarith)
                      linarith
            · rcases le_total y (529/512:ℝ) with hc | hc
              · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
                have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_556 (x + y) (by linarith) (by linarith)
                have hw5 : (38680157/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1241 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (1023/512:ℝ) with hc | hc
                · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
                  have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                  have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                  have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                  have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                  have hw5 : (191511939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1266 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
                  have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                  have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                  have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1314 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (509/256:ℝ) with hc | hc
          · rcases le_total x (1033/512:ℝ) with hc | hc
            · rcases le_total y (539/512:ℝ) with hc | hc
              · rcases le_total z (1013/512:ℝ) with hc | hc
                · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
                  have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_41 y (by linarith) (by linarith)
                  have hw2 : (4884069333/10000000000000:ℝ) ≤ wfun z := wc_132 z (by linarith) (by linarith)
                  have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                  have hw5 : (449469/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1219 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
                  have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_41 y (by linarith) (by linarith)
                  have hw2 : (3192232409/10000000000000:ℝ) ≤ wfun z := wc_165 z (by linarith) (by linarith)
                  have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                  have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
                  have hw5 : (38980307/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1240 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
                have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                have hw5 : (38680157/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1241 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
              have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
              have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
              have hw5 : (76765783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1242 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (1033/512:ℝ) with hc | hc
            · rcases le_total y (539/512:ℝ) with hc | hc
              · rcases le_total z (1023/512:ℝ) with hc | hc
                · rcases le_total x (2061/1024:ℝ) with hc | hc
                  · rcases le_total y (1073/1024:ℝ) with hc | hc
                    · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_242 x (by linarith) (by linarith)
                      have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_40 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                      have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_484 (y + z) (by linarith) (by linarith)
                      have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1264 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_242 x (by linarith) (by linarith)
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_72 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                      have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                      have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_534 (y + z) (by linarith) (by linarith)
                      have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1290 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (1073/1024:ℝ) with hc | hc
                    · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_246 x (by linarith) (by linarith)
                      have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_40 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                      have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                      have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_484 (y + z) (by linarith) (by linarith)
                      have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1290 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_246 x (by linarith) (by linarith)
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_72 y (by linarith) (by linarith)
                      have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                      have hw3 : (9367789/78125000000:ℝ) ≤ wfun (x + y) := wc_582 (x + y) (by linarith) (by linarith)
                      have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_534 (y + z) (by linarith) (by linarith)
                      have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1312 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total x (2061/1024:ℝ) with hc | hc
                  · rcases le_total y (1073/1024:ℝ) with hc | hc
                    · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_242 x (by linarith) (by linarith)
                      have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_40 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
                      have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_555 (y + z) (by linarith) (by linarith)
                      have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1312 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_242 x (by linarith) (by linarith)
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_72 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                      have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
                      have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1340 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (1073/1024:ℝ) with hc | hc
                    · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_246 x (by linarith) (by linarith)
                      have hw1 : (349265369/5000000000000:ℝ) ≤ wfun y := wc_40 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
                      have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_555 (y + z) (by linarith) (by linarith)
                      have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1340 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_246 x (by linarith) (by linarith)
                      have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_72 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                      have hw3 : (9367789/78125000000:ℝ) ≤ wfun (x + y) := wc_582 (x + y) (by linarith) (by linarith)
                      have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
                      have hw5 : (568693187/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1367 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total z (1023/512:ℝ) with hc | hc
                · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
                  have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                  have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                  have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                  have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1314 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                  have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                  have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1369 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (539/512:ℝ) with hc | hc
              · rcases le_total z (1023/512:ℝ) with hc | hc
                · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
                  have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_41 y (by linarith) (by linarith)
                  have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_219 z (by linarith) (by linarith)
                  have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                  have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
                  have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1314 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
                  have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_41 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_233 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                  have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                  have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                  have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1369 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                have hw3 : (1810022563/10000000000000:ℝ) ≤ wfun (x + y) := wc_589 (x + y) (by linarith) (by linarith)
                have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_557 (y + z) (by linarith) (by linarith)
                have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1370 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (267/256:ℝ) with hc | hc
        · rcases le_total z (509/256:ℝ) with hc | hc
          · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
            have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_133 z (by linarith) (by linarith)
            have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
            have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1222 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (1043/512:ℝ) with hc | hc
            · rcases le_total y (529/512:ℝ) with hc | hc
              · have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw5 : (190040129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1267 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1315 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (21355581/2500000000000:ℝ) ≤ wfun x := wc_250 x (by linarith) (by linarith)
              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_220 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 z (by linarith) (by linarith))
              have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
              have hw5 : (43578037/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1316 (x + y + z) (by linarith) (by linarith)
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
            have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_487 (y + z) (by linarith) (by linarith)
            have hw5 : (551493311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1372 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (519/256:ℝ) with hc | hc
      · rcases le_total y (267/256:ℝ) with hc | hc
        · rcases le_total z (519/256:ℝ) with hc | hc
          · rcases le_total x (1033/512:ℝ) with hc | hc
            · rcases le_total y (529/512:ℝ) with hc | hc
              · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
                have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
                have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_486 (y + z) (by linarith) (by linarith)
                have hw5 : (190040129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1267 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (1033/512:ℝ) with hc | hc
                · rcases le_total x (2061/1024:ℝ) with hc | hc
                  · rcases le_total y (1063/1024:ℝ) with hc | hc
                    · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_242 x (by linarith) (by linarith)
                      have hw1 : (2957142633/10000000000000:ℝ) ≤ wfun y := wc_18 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                      have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
                      have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_555 (y + z) (by linarith) (by linarith)
                      have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1312 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_242 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_25 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                      have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
                      have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
                      have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1340 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_246 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                    have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_565 (x + y) (by linarith) (by linarith)
                    have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
                    have hw5 : (91007427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1341 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
                  have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                  have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_556 (x + y) (by linarith) (by linarith)
                  have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                  have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1369 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (529/512:ℝ) with hc | hc
              · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
                have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_556 (x + y) (by linarith) (by linarith)
                have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_486 (y + z) (by linarith) (by linarith)
                have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1315 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
                have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_557 (y + z) (by linarith) (by linarith)
                have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1370 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (1033/512:ℝ) with hc | hc
            · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
              have hw3 : (22330933/2500000000000:ℝ) ≤ wfun (x + y) := wc_486 (x + y) (by linarith) (by linarith)
              have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
              have hw5 : (69466449/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1371 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
              have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_557 (x + y) (by linarith) (by linarith)
              have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
              have hw5 : (404289107/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1435 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (519/256:ℝ) with hc | hc
          · rcases le_total x (1033/512:ℝ) with hc | hc
            · rcases le_total y (539/512:ℝ) with hc | hc
              · rcases le_total z (1033/512:ℝ) with hc | hc
                · rcases le_total x (2061/1024:ℝ) with hc | hc
                  · have hw0 : (543159341/10000000000000:ℝ) ≤ wfun x := wc_242 x (by linarith) (by linarith)
                    have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_41 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                    have hw3 : (172511147/2500000000000:ℝ) ≤ wfun (x + y) := wc_571 (x + y) (by linarith) (by linarith)
                    have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                    have hw5 : (566506871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1368 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_246 x (by linarith) (by linarith)
                    have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_41 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                    have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_581 (x + y) (by linarith) (by linarith)
                    have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
                    have hw5 : (68963139/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1401 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
                  have hw1 : (160574441/10000000000000:ℝ) ≤ wfun y := wc_41 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                  have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                  have hw4 : (591930551/5000000000000:ℝ) ≤ wfun (y + z) := wc_584 (y + z) (by linarith) (by linarith)
                  have hw5 : (821066057/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1433 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (27945219/1000000000000:ℝ) ≤ wfun x := wc_243 x (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_585 (y + z) (by linarith) (by linarith)
                have hw5 : (814792219/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1434 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_248 x (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
              have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
              have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
              have hw5 : (404289107/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1435 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (13164037/10000000000000:ℝ) ≤ wfun x := wc_244 x (by linarith) (by linarith)
            have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
            have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_590 (y + z) (by linarith) (by linarith)
            have hw5 : (1097277581/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1472 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (267/256:ℝ) with hc | hc
        · rcases le_total z (519/256:ℝ) with hc | hc
          · rcases le_total x (1043/512:ℝ) with hc | hc
            · rcases le_total y (529/512:ℝ) with hc | hc
              · have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
                have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_486 (y + z) (by linarith) (by linarith)
                have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1370 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_19 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_584 (x + y) (by linarith) (by linarith)
                have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_557 (y + z) (by linarith) (by linarith)
                have hw5 : (814792219/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1434 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (21355581/2500000000000:ℝ) ≤ wfun x := wc_250 x (by linarith) (by linarith)
              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
              have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_585 (x + y) (by linarith) (by linarith)
              have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_487 (y + z) (by linarith) (by linarith)
              have hw5 : (404289107/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1435 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
            have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
            have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
            have hw5 : (1097277581/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1472 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_590 (x + y) (by linarith) (by linarith)
          have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_576 (y + z) (by linarith) (by linarith)
          have hw5 : (270178737/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1473 (x + y + z) (by linarith) (by linarith)
          linarith

end Zeta23Ext.Bridge.FourPoint
