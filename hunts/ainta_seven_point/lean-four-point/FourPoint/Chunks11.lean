import FourPoint.Cells

/-! Chunk module 11 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_1 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
            have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_76 z (by linarith) (by linarith)
            linarith
          · rcases le_total y (131/128:ℝ) with hc | hc
            · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_76 z (by linarith) (by linarith)
              have hw4 : (269743281/5000000000000:ℝ) ≤ wfun (y + z) := wc_188 (y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (247/128:ℝ) with hc | hc
              · have hw2 : (9113139537/5000000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
                have hw4 : (288828359/5000000000000:ℝ) ≤ wfun (y + z) := wc_189 (y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (267/256:ℝ) with hc | hc
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · rcases le_total z (499/256:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw2 : (6028900351/5000000000000:ℝ) ≤ wfun z := wc_77 z (by linarith) (by linarith)
                      have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                      have hw4 : (15105971/250000000000:ℝ) ≤ wfun (y + z) := wc_197 (y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw2 : (688065547/1000000000000:ℝ) ≤ wfun z := wc_80 z (by linarith) (by linarith)
                      have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_208 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                      linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                    have hw2 : (6731724963/10000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                    have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw2 : (6731724963/10000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                    have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_198 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                    linarith
                  · have hw2 : (6731724963/10000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                    have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_172 (x + y) (by linarith) (by linarith)
                    have hw5 : (60567/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_456 (x + y + z) (by linarith) (by linarith)
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
                    · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  linarith
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    linarith
                  · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                    have hw5 : (60567/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_456 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (257/256:ℝ) with hc | hc
                · have hw0 : (12267823741/5000000000000:ℝ) ≤ wfun x := by
                    rcases le_total x (1:ℝ) with hq00 | hq00
                    · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_6 x (by linarith) (by linarith))
                  have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
                  have hw5 : (59421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_457 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw4 : (21491553/2500000000000:ℝ) ≤ wfun (y + z) := wc_307 (y + z) (by linarith) (by linarith)
                    have hw5 : (39204539/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_513 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                    have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
                    have hw5 : (24278963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_552 (x + y + z) (by linarith) (by linarith)
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
                    · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  linarith
                · rcases le_total y (257/256:ℝ) with hc | hc
                  · have hw1 : (12267823741/5000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (1:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_6 y (by linarith) (by linarith))
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_198 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                    linarith
                  · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := wc_9 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                    have hw5 : (60567/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_456 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (267/256:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (1:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                  have hw5 : (59421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_457 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (257/256:ℝ) with hc | hc
                  · have hw1 : (12267823741/5000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (1:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_6 y (by linarith) (by linarith))
                    have hw5 : (39204539/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_513 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := wc_9 y (by linarith) (by linarith)
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                    have hw5 : (24278963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_552 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (257/128:ℝ) with hc | hc
              · rcases le_total x (267/256:ℝ) with hc | hc
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · rcases le_total z (509/256:ℝ) with hc | hc
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                          have hw3 : (94460693/2000000000000:ℝ) ≤ wfun (x + y) := wc_154 (x + y) (by linarith) (by linarith)
                          have hw5 : (31471/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_453 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                          have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_162 (x + y) (by linarith) (by linarith)
                          have hw5 : (1064707/250000000000:ℝ) ≤ wfun (x + y + z) := wc_493 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                          have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_162 (x + y) (by linarith) (by linarith)
                          have hw5 : (1064707/250000000000:ℝ) ≤ wfun (x + y + z) := wc_493 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · rcases le_total z (1013/512:ℝ) with hc | hc
                          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                            have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                            have hw2 : (4884069333/10000000000000:ℝ) ≤ wfun z := wc_88 z (by linarith) (by linarith)
                            have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_165 (x + y) (by linarith) (by linarith)
                            have hw5 : (164514637/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_509 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                            have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                            have hw2 : (3192232409/10000000000000:ℝ) ≤ wfun z := wc_105 z (by linarith) (by linarith)
                            have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_165 (x + y) (by linarith) (by linarith)
                            have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_530 (x + y + z) (by linarith) (by linarith)
                            linarith
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (94460693/2000000000000:ℝ) ≤ wfun (x + y) := wc_154 (x + y) (by linarith) (by linarith)
                          have hw5 : (81469089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_510 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · rcases le_total z (1023/512:ℝ) with hc | hc
                          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                            have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                            have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                            have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_162 (x + y) (by linarith) (by linarith)
                            have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                            have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_530 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                            have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                              rcases le_total z (2:ℝ) with hq20 | hq20
                              · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                              exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                            have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_162 (x + y) (by linarith) (by linarith)
                            have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                            have hw5 : (636617867/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_548 (x + y + z) (by linarith) (by linarith)
                            linarith
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · rcases le_total z (1023/512:ℝ) with hc | hc
                          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                            have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                            have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                            have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_162 (x + y) (by linarith) (by linarith)
                            have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_530 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                            have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                              rcases le_total z (2:ℝ) with hq20 | hq20
                              · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                              exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                            have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_162 (x + y) (by linarith) (by linarith)
                            have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                            have hw5 : (636617867/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_548 (x + y + z) (by linarith) (by linarith)
                            linarith
                        · rcases le_total z (1023/512:ℝ) with hc | hc
                          · rcases le_total x (1063/1024:ℝ) with hc | hc
                            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                              have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                              have hw3 : (54451693/250000000000:ℝ) ≤ wfun (x + y) := wc_164 (x + y) (by linarith) (by linarith)
                              have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                              have hw5 : (79960111/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_547 (x + y + z) (by linarith) (by linarith)
                              linarith
                            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                              have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                              have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                              have hw3 : (1392763463/5000000000000:ℝ) ≤ wfun (x + y) := wc_169 (x + y) (by linarith) (by linarith)
                              have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                              have hw5 : (402392913/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_565 (x + y + z) (by linarith) (by linarith)
                              linarith
                          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                            have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                              rcases le_total z (2:ℝ) with hq20 | hq20
                              · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                              exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                            have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_165 (x + y) (by linarith) (by linarith)
                            have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                            have hw5 : (49160907/500000000000:ℝ) ≤ wfun (x + y + z) := wc_587 (x + y + z) (by linarith) (by linarith)
                            linarith
                  · rcases le_total z (509/256:ℝ) with hc | hc
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                        have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                        have hw3 : (264638553/1250000000000:ℝ) ≤ wfun (x + y) := wc_166 (x + y) (by linarith) (by linarith)
                        have hw5 : (20172571/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_511 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                        have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                        have hw3 : (3366163659/10000000000000:ℝ) ≤ wfun (x + y) := wc_171 (x + y) (by linarith) (by linarith)
                        have hw5 : (17805471/500000000000:ℝ) ≤ wfun (x + y + z) := wc_532 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                        have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                          rcases le_total z (2:ℝ) with hq20 | hq20
                          · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                        have hw3 : (264638553/1250000000000:ℝ) ≤ wfun (x + y) := wc_166 (x + y) (by linarith) (by linarith)
                        have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                        have hw5 : (624547701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_550 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                        have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                          rcases le_total z (2:ℝ) with hq20 | hq20
                          · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                        have hw3 : (3366163659/10000000000000:ℝ) ≤ wfun (x + y) := wc_171 (x + y) (by linarith) (by linarith)
                        have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                        have hw5 : (9646207/100000000000:ℝ) ≤ wfun (x + y + z) := wc_589 (x + y + z) (by linarith) (by linarith)
                        linarith
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · rcases le_total z (509/256:ℝ) with hc | hc
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                          have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_165 (x + y) (by linarith) (by linarith)
                          have hw5 : (81469089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_510 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                          have hw3 : (343008739/1000000000000:ℝ) ≤ wfun (x + y) := wc_170 (x + y) (by linarith) (by linarith)
                          have hw5 : (89884553/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_531 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                        have hw3 : (3366163659/10000000000000:ℝ) ≤ wfun (x + y) := wc_171 (x + y) (by linarith) (by linarith)
                        have hw5 : (17805471/500000000000:ℝ) ≤ wfun (x + y + z) := wc_532 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_165 (x + y) (by linarith) (by linarith)
                          have hw5 : (315273331/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_549 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                            rcases le_total z (2:ℝ) with hq20 | hq20
                            · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                          have hw3 : (343008739/1000000000000:ℝ) ≤ wfun (x + y) := wc_170 (x + y) (by linarith) (by linarith)
                          have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_247 (y + z) (by linarith) (by linarith)
                          have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_588 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                          rcases le_total z (2:ℝ) with hq20 | hq20
                          · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                        have hw3 : (3366163659/10000000000000:ℝ) ≤ wfun (x + y) := wc_171 (x + y) (by linarith) (by linarith)
                        have hw5 : (9646207/100000000000:ℝ) ≤ wfun (x + y + z) := wc_589 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total z (509/256:ℝ) with hc | hc
                    · have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                      have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_172 (x + y) (by linarith) (by linarith)
                      have hw5 : (154654989/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_551 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                      have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_172 (x + y) (by linarith) (by linarith)
                      have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                      have hw5 : (1361028853/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_657 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total x (267/256:ℝ) with hc | hc
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · rcases le_total z (519/256:ℝ) with hc | hc
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                          have hw3 : (94460693/2000000000000:ℝ) ≤ wfun (x + y) := wc_154 (x + y) (by linarith) (by linarith)
                          have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_305 (y + z) (by linarith) (by linarith)
                          have hw5 : (315273331/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_549 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                          have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_162 (x + y) (by linarith) (by linarith)
                          have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                          have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_588 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                          have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_162 (x + y) (by linarith) (by linarith)
                          have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_305 (y + z) (by linarith) (by linarith)
                          have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_588 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                          have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_165 (x + y) (by linarith) (by linarith)
                          have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                          have hw5 : (69357131/500000000000:ℝ) ≤ wfun (x + y + z) := wc_655 (x + y + z) (by linarith) (by linarith)
                          linarith
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw3 : (115843823/2500000000000:ℝ) ≤ wfun (x + y) := wc_155 (x + y) (by linarith) (by linarith)
                        have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                        have hw5 : (274801629/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_656 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw3 : (1145460727/10000000000000:ℝ) ≤ wfun (x + y) := wc_163 (x + y) (by linarith) (by linarith)
                        have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                        have hw5 : (1850155147/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_718 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total z (519/256:ℝ) with hc | hc
                    · rcases le_total x (529/512:ℝ) with hc | hc
                      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                        have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                        have hw3 : (264638553/1250000000000:ℝ) ≤ wfun (x + y) := wc_166 (x + y) (by linarith) (by linarith)
                        have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                        have hw5 : (274801629/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_656 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                        have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                        have hw3 : (3366163659/10000000000000:ℝ) ≤ wfun (x + y) := wc_171 (x + y) (by linarith) (by linarith)
                        have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                        have hw5 : (1850155147/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_718 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                      have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                      have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_370 (y + z) (by linarith) (by linarith)
                      have hw5 : (591952751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_738 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · rcases le_total z (519/256:ℝ) with hc | hc
                    · rcases le_total x (539/512:ℝ) with hc | hc
                      · rcases le_total y (529/512:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                          have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                          have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_165 (x + y) (by linarith) (by linarith)
                          have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_305 (y + z) (by linarith) (by linarith)
                          have hw5 : (69357131/500000000000:ℝ) ≤ wfun (x + y + z) := wc_655 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                          have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                          have hw3 : (343008739/1000000000000:ℝ) ≤ wfun (x + y) := wc_170 (x + y) (by linarith) (by linarith)
                          have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                          have hw5 : (933899467/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_717 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                        have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                        have hw3 : (3366163659/10000000000000:ℝ) ≤ wfun (x + y) := wc_171 (x + y) (by linarith) (by linarith)
                        have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                        have hw5 : (1850155147/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_718 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                      have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                      have hw5 : (591952751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_738 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_172 (x + y) (by linarith) (by linarith)
                    have hw4 : (162913869/2500000000000:ℝ) ≤ wfun (y + z) := wc_360 (y + z) (by linarith) (by linarith)
                    have hw5 : (1161826227/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_739 (x + y + z) (by linarith) (by linarith)
                    linarith
      · rcases le_total z (63/32:ℝ) with hc | hc
        · rcases le_total x (131/128:ℝ) with hc | hc
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
              rcases le_total x (1:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
            have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
            have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_76 z (by linarith) (by linarith)
            have hw3 : (12244337/312500000000:ℝ) ≤ wfun (x + y) := wc_159 (x + y) (by linarith) (by linarith)
            linarith
          · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
            have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_76 z (by linarith) (by linarith)
            have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_175 (x + y) (by linarith) (by linarith)
            linarith
        · rcases le_total x (131/128:ℝ) with hc | hc
          · rcases le_total y (141/128:ℝ) with hc | hc
            · rcases le_total z (257/128:ℝ) with hc | hc
              · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                  rcases le_total x (1:ℝ) with hq00 | hq00
                  · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
                have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
                have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
                have hw5 : (58303/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_458 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                  rcases le_total x (1:ℝ) with hq00 | hq00
                  · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
                have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
                have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (913271/15625000000:ℝ) ≤ wfun (x + y + z) := wc_554 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw1 : (11778340313/10000000000000:ℝ) ≤ wfun y := wc_67 y (by linarith) (by linarith)
              have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
              have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (563044583/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_555 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (141/128:ℝ) with hc | hc
            · rcases le_total z (257/128:ℝ) with hc | hc
              · rcases le_total x (267/256:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (4615617497/10000000000000:ℝ) ≤ wfun (x + y) := wc_173 (x + y) (by linarith) (by linarith)
                  have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
                  have hw5 : (297800559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_553 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (2045420557/2500000000000:ℝ) ≤ wfun (x + y) := wc_177 (x + y) (by linarith) (by linarith)
                  have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
                  have hw5 : (655310061/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_659 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
                have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
                have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (2238382569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_741 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (11778340313/10000000000000:ℝ) ≤ wfun y := wc_67 y (by linarith) (by linarith)
              have hw3 : (48584483/40000000000:ℝ) ≤ wfun (x + y) := wc_178 (x + y) (by linarith) (by linarith)
              have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_742 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (17/16:ℝ) with hc | hc
      · rcases le_total z (63/32:ℝ) with hc | hc
        · rcases le_total x (141/128:ℝ) with hc | hc
          · rcases le_total y (131/128:ℝ) with hc | hc
            · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_76 z (by linarith) (by linarith)
              have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
              have hw4 : (269743281/5000000000000:ℝ) ≤ wfun (y + z) := wc_188 (y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_76 z (by linarith) (by linarith)
              have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
              linarith
          · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
            have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_76 z (by linarith) (by linarith)
            have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_175 (x + y) (by linarith) (by linarith)
            linarith
        · rcases le_total x (141/128:ℝ) with hc | hc
          · rcases le_total y (131/128:ℝ) with hc | hc
            · rcases le_total z (257/128:ℝ) with hc | hc
              · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
                have hw5 : (58303/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_458 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
                have hw5 : (913271/15625000000:ℝ) ≤ wfun (x + y + z) := wc_554 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (257/128:ℝ) with hc | hc
              · rcases le_total x (277/256:ℝ) with hc | hc
                · rcases le_total y (267/256:ℝ) with hc | hc
                  · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_172 (x + y) (by linarith) (by linarith)
                    have hw5 : (24278963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_552 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (4243616393/5000000000000:ℝ) ≤ wfun (x + y) := wc_176 (x + y) (by linarith) (by linarith)
                    have hw5 : (1335527067/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_658 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (2045420557/2500000000000:ℝ) ≤ wfun (x + y) := wc_177 (x + y) (by linarith) (by linarith)
                  have hw5 : (655310061/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_659 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
                have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
                have hw5 : (2238382569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_741 (x + y + z) (by linarith) (by linarith)
                linarith
          · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
            have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_175 (x + y) (by linarith) (by linarith)
            have hw5 : (271285583/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_556 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
        have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
        have hw3 : (2788858101/2500000000000:ℝ) ≤ wfun (x + y) := by
          rcases le_total (x + y) (9/4:ℝ) with hq30 | hq30
          · exact le_trans (by norm_num) (wc_179 (x + y) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_182 (x + y) (by linarith) (by linarith))
        have hw5 : (13029/2500000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_460 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_757 (x + y + z) (by linarith) (by linarith))
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
              have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
              have hw4 : (79711817/10000000000000:ℝ) ≤ wfun (y + z) := wc_310 (y + z) (by linarith) (by linarith)
              have hw5 : (56143/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_459 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
              have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (563044583/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_555 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (131/128:ℝ) with hc | hc
            · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
              have hw4 : (79711817/10000000000000:ℝ) ≤ wfun (y + z) := wc_310 (y + z) (by linarith) (by linarith)
              have hw5 : (563044583/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_555 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (267/128:ℝ) with hc | hc
              · have hw2 : (18186303/400000000000:ℝ) ≤ wfun z := wc_156 z (by linarith) (by linarith)
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
                have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (2238382569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_741 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw2 : (4789633321/10000000000000:ℝ) ≤ wfun z := wc_172 z (by linarith) (by linarith)
                have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
                have hw4 : (5096134953/10000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (600628743/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_752 (x + y + z) (by linarith) (by linarith)
                linarith
        · have hw2 : (48584483/40000000000:ℝ) ≤ wfun z := wc_178 z (by linarith) (by linarith)
          have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_386 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_389 (y + z) (by linarith) (by linarith))
          have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := by
            rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
            · exact le_trans (by norm_num) (wc_742 (x + y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_757 (x + y + z) (by linarith) (by linarith))
          linarith
      · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
        have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_160 z (by linarith) (by linarith)
        have hw3 : (182240171/5000000000000:ℝ) ≤ wfun (x + y) := wc_160 (x + y) (by linarith) (by linarith)
        have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_386 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_392 (y + z) (by linarith) (by linarith))
        have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_742 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_758 (x + y + z) (by linarith) (by linarith))
        linarith
    · rcases le_total y (17/16:ℝ) with hc | hc
      · rcases le_total z (17/8:ℝ) with hc | hc
        · rcases le_total x (141/128:ℝ) with hc | hc
          · rcases le_total y (131/128:ℝ) with hc | hc
            · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
              have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
              have hw4 : (79711817/10000000000000:ℝ) ≤ wfun (y + z) := wc_310 (y + z) (by linarith) (by linarith)
              have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_742 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
              have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
              have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (600628743/1250000000000:ℝ) ≤ wfun (x + y + z) := by
                rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
                · exact le_trans (by norm_num) (wc_752 (x + y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_755 (x + y + z) (by linarith) (by linarith))
              linarith
          · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
            have hw2 : (42177537/1000000000000:ℝ) ≤ wfun z := wc_158 z (by linarith) (by linarith)
            have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_175 (x + y) (by linarith) (by linarith)
            have hw4 : (75856633/10000000000000:ℝ) ≤ wfun (y + z) := wc_311 (y + z) (by linarith) (by linarith)
            have hw5 : (600628743/1250000000000:ℝ) ≤ wfun (x + y + z) := by
              rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
              · exact le_trans (by norm_num) (wc_752 (x + y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_757 (x + y + z) (by linarith) (by linarith))
            linarith
        · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
          have hw2 : (48584483/40000000000:ℝ) ≤ wfun z := wc_178 z (by linarith) (by linarith)
          have hw3 : (182240171/5000000000000:ℝ) ≤ wfun (x + y) := wc_160 (x + y) (by linarith) (by linarith)
          have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_386 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_389 (y + z) (by linarith) (by linarith))
          have hw5 : (8382305677/10000000000000:ℝ) ≤ wfun (x + y + z) := by
            rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
            · exact le_trans (by norm_num) (wc_754 (x + y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_758 (x + y + z) (by linarith) (by linarith))
          linarith
      · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
        have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
        have hw2 : (182240171/5000000000000:ℝ) ≤ wfun z := wc_160 z (by linarith) (by linarith)
        have hw3 : (2788858101/2500000000000:ℝ) ≤ wfun (x + y) := by
          rcases le_total (x + y) (9/4:ℝ) with hq30 | hq30
          · exact le_trans (by norm_num) (wc_179 (x + y) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_182 (x + y) (by linarith) (by linarith))
        have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_386 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_392 (y + z) (by linarith) (by linarith))
        have hw5 : (8382305677/10000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_754 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_760 (x + y + z) (by linarith) (by linarith))
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_11 (x y z : ℝ) (hx1 : (1063/1024:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (1073/1024:ℝ) with hc | hc
  · rcases le_total x (2131/2048:ℝ) with hc | hc
    · rcases le_total y (4057/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
            have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_559 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
            have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_568 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
            have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_570 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
            have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_577 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
            have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_570 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8119/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
              have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
              have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
            have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_580 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8119/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
              have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (4057/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8109/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
              have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_569 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
              have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8109/4096:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
              have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_578 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8109/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
              have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8109/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8119/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
              have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8119/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_590 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8119/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8119/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total x (2131/2048:ℝ) with hc | hc
    · rcases le_total y (4057/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
            have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_580 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
            have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_592 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
            have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_596 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
            have hw5 : (1157601093/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_604 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
            have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_596 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8119/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
            have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_609 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
            have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_238 (x + y) (by linarith) (by linarith)
            have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
            have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_622 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (4057/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8109/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
              have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8109/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
            have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_609 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8109/4096:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
              have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
              have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8119/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
              have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8119/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8119/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
              have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
              have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8119/4096:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
              have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_21 (x y z : ℝ) (hx1 : (539/512:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (1013/512:ℝ) with hc | hc
  · rcases le_total z (529/512:ℝ) with hc | hc
    · have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
      have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_530 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2021/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
            have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_545 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4037/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
                have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_561 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_230 (y + z) (by linarith) (by linarith)
                have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_572 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (4037/2048:ℝ) with hc | hc
              · have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
                have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_572 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_230 (y + z) (by linarith) (by linarith)
                have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_582 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
            have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_563 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                  have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                  have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
                  have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                  have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                  have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                  have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
                have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_598 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_611 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (2021/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
            have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_563 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
            have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
            have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_584 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
            have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_584 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
            have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
            have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_613 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (529/512:ℝ) with hc | hc
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_224 (y + z) (by linarith) (by linarith)
          have hw5 : (160690591/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_546 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
          have hw5 : (808657969/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_564 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
        have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
        have hw5 : (402392913/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_565 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
                have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_582 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_598 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_321 (x + y) (by linarith) (by linarith)
              have hw5 : (549643007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_599 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                  have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                  have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                    have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (5774823/625000000000:ℝ) ≤ wfun (x + y) := wc_299 (x + y) (by linarith) (by linarith)
                    have hw5 : (659665673/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_630 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_316 (x + y) (by linarith) (by linarith)
                    have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_640 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                  have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_631 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                    have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_319 (x + y) (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                    have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_647 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                    have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                    have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_666 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                have hw5 : (262917659/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_632 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_649 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_611 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                have hw5 : (262917659/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_632 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
              have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
              have hw5 : (655719053/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_633 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                  have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                  have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_648 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2131/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                  have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_20 z (by linarith) (by linarith)
                  have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                  have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                  have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                  have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_688 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_243 (y + z) (by linarith) (by linarith)
                have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_675 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_257 (y + z) (by linarith) (by linarith)
                have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_689 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
            have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_613 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (2171/2048:ℝ) with hc | hc
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_649 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_675 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (5858063/1000000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
              have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
              have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_676 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (1063/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
            have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
            have hw5 : (1420672477/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_651 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
            have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
            have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
            have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_75 (x y z : ℝ) (hx1 : (121/64:ℝ) ≤ x) (hx2 : x ≤ (141/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (131/64:ℝ) with hc | hc
  · rcases le_total y (131/64:ℝ) with hc | hc
    · rcases le_total z (131/64:ℝ) with hc | hc
      · rcases le_total x (63/32:ℝ) with hc | hc
        · have hw0 : (795663039/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
          linarith
        · rcases le_total y (63/32:ℝ) with hc | hc
          · have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_76 y (by linarith) (by linarith)
            linarith
          · linarith
      · linarith
    · linarith
  · linarith

end Zeta23Ext.Bridge.FourPoint
