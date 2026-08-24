import FourPoint.Cells

/-! Chunk module 7 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_0 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (17/16:ℝ) with hc | hc
  · rcases le_total y (17/16:ℝ) with hc | hc
    · rcases le_total z (17/16:ℝ) with hc | hc
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
                have hw4 : (42177537/1000000000000:ℝ) ≤ wfun (y + z) := wc_158 (y + z) (by linarith) (by linarith)
                have hw5 : (40865677/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_309 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (267/256:ℝ) with hc | hc
                · rcases le_total z (267/256:ℝ) with hc | hc
                  · rcases le_total x (519/512:ℝ) with hc | hc
                    · have hw0 : (4015256583/2500000000000:ℝ) ≤ wfun x := wc_8 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                      have hw4 : (18186303/400000000000:ℝ) ≤ wfun (y + z) := wc_156 (y + z) (by linarith) (by linarith)
                      have hw5 : (329975333/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_359 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_10 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                      have hw3 : (1284381/156250000000:ℝ) ≤ wfun (x + y) := wc_153 (x + y) (by linarith) (by linarith)
                      have hw4 : (18186303/400000000000:ℝ) ≤ wfun (y + z) := wc_156 (y + z) (by linarith) (by linarith)
                      have hw5 : (569820171/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_368 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw4 : (259706701/1250000000000:ℝ) ≤ wfun (y + z) := wc_167 (y + z) (by linarith) (by linarith)
                    have hw5 : (215107179/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_371 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := wc_9 x (by linarith) (by linarith)
                  have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                  have hw4 : (2001469121/10000000000000:ℝ) ≤ wfun (y + z) := wc_168 (y + z) (by linarith) (by linarith)
                  have hw5 : (419583999/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_372 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total y (131/128:ℝ) with hc | hc
          · rcases le_total z (131/128:ℝ) with hc | hc
            · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
                rcases le_total z (1:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
              linarith
            · rcases le_total x (267/256:ℝ) with hc | hc
              · rcases le_total y (257/256:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw1 : (12267823741/5000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (1:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_6 y (by linarith) (by linarith))
                  have hw5 : (20953831/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_308 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (267/256:ℝ) with hc | hc
                  · rcases le_total x (529/512:ℝ) with hc | hc
                    · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                      have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := wc_9 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                      have hw5 : (329975333/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_359 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total y (519/512:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                        have hw1 : (4015256583/2500000000000:ℝ) ≤ wfun y := wc_8 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                        have hw3 : (83791953/10000000000000:ℝ) ≤ wfun (x + y) := wc_152 (x + y) (by linarith) (by linarith)
                        have hw5 : (288536823/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_367 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                        have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := wc_10 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                        have hw3 : (94460693/2000000000000:ℝ) ≤ wfun (x + y) := wc_154 (x + y) (by linarith) (by linarith)
                        have hw4 : (1284381/156250000000:ℝ) ≤ wfun (y + z) := wc_153 (y + z) (by linarith) (by linarith)
                        have hw5 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_370 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                    have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := wc_9 y (by linarith) (by linarith)
                    have hw4 : (18186303/400000000000:ℝ) ≤ wfun (y + z) := wc_156 (y + z) (by linarith) (by linarith)
                    have hw5 : (215107179/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_371 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (257/256:ℝ) with hc | hc
                · have hw1 : (12267823741/5000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (1:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_6 y (by linarith) (by linarith))
                  have hw5 : (635452827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_361 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (267/256:ℝ) with hc | hc
                  · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := wc_9 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                    have hw5 : (215107179/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_371 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := wc_9 y (by linarith) (by linarith)
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                    have hw4 : (18186303/400000000000:ℝ) ≤ wfun (y + z) := wc_156 (y + z) (by linarith) (by linarith)
                    have hw5 : (1629257293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_379 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total z (131/128:ℝ) with hc | hc
            · rcases le_total x (267/256:ℝ) with hc | hc
              · rcases le_total y (267/256:ℝ) with hc | hc
                · rcases le_total z (257/256:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw2 : (12267823741/5000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (1:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_6 z (by linarith) (by linarith))
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                    have hw5 : (21491553/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_307 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (529/512:ℝ) with hc | hc
                    · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := wc_9 z (by linarith) (by linarith)
                      have hw3 : (115843823/2500000000000:ℝ) ≤ wfun (x + y) := wc_155 (x + y) (by linarith) (by linarith)
                      have hw5 : (329975333/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_359 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                      have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                      have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := wc_9 z (by linarith) (by linarith)
                      have hw3 : (1145460727/10000000000000:ℝ) ≤ wfun (x + y) := wc_163 (x + y) (by linarith) (by linarith)
                      have hw5 : (569820171/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_368 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (257/256:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                    have hw2 : (12267823741/5000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (1:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_6 z (by linarith) (by linarith))
                    have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                    have hw5 : (162913869/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_360 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                    have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := wc_9 z (by linarith) (by linarith)
                    have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                    have hw4 : (18186303/400000000000:ℝ) ≤ wfun (y + z) := wc_156 (y + z) (by linarith) (by linarith)
                    have hw5 : (215107179/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_371 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (267/256:ℝ) with hc | hc
                · rcases le_total z (257/256:ℝ) with hc | hc
                  · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw2 : (12267823741/5000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (1:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_6 z (by linarith) (by linarith))
                    have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                    have hw5 : (162913869/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_360 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := wc_9 z (by linarith) (by linarith)
                    have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                    have hw5 : (215107179/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_371 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (1:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
                  have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_172 (x + y) (by linarith) (by linarith)
                  have hw5 : (419583999/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_372 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (267/256:ℝ) with hc | hc
              · rcases le_total y (267/256:ℝ) with hc | hc
                · rcases le_total z (267/256:ℝ) with hc | hc
                  · rcases le_total x (529/512:ℝ) with hc | hc
                    · rcases le_total y (529/512:ℝ) with hc | hc
                      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                        have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                        have hw3 : (94460693/2000000000000:ℝ) ≤ wfun (x + y) := wc_154 (x + y) (by linarith) (by linarith)
                        have hw4 : (115843823/2500000000000:ℝ) ≤ wfun (y + z) := wc_155 (y + z) (by linarith) (by linarith)
                        have hw5 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_370 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                        have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_162 (x + y) (by linarith) (by linarith)
                        have hw4 : (1145460727/10000000000000:ℝ) ≤ wfun (y + z) := wc_163 (y + z) (by linarith) (by linarith)
                        have hw5 : (124770657/500000000000:ℝ) ≤ wfun (x + y + z) := wc_377 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total y (529/512:ℝ) with hc | hc
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                        have hw1 : (1175437333/2500000000000:ℝ) ≤ wfun y := wc_12 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                        have hw3 : (291856019/2500000000000:ℝ) ≤ wfun (x + y) := wc_162 (x + y) (by linarith) (by linarith)
                        have hw4 : (115843823/2500000000000:ℝ) ≤ wfun (y + z) := wc_155 (y + z) (by linarith) (by linarith)
                        have hw5 : (124770657/500000000000:ℝ) ≤ wfun (x + y + z) := wc_377 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                        have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_17 y (by linarith) (by linarith)
                        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                        have hw3 : (269688311/1250000000000:ℝ) ≤ wfun (x + y) := wc_165 (x + y) (by linarith) (by linarith)
                        have hw4 : (1145460727/10000000000000:ℝ) ≤ wfun (y + z) := wc_163 (y + z) (by linarith) (by linarith)
                        have hw5 : (1670535297/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_378 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                    have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                    have hw4 : (259706701/1250000000000:ℝ) ≤ wfun (y + z) := wc_167 (y + z) (by linarith) (by linarith)
                    have hw5 : (1629257293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_379 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                  have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                  have hw4 : (2001469121/10000000000000:ℝ) ≤ wfun (y + z) := wc_168 (y + z) (by linarith) (by linarith)
                  have hw5 : (1589247651/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_380 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (267/256:ℝ) with hc | hc
                · rcases le_total z (267/256:ℝ) with hc | hc
                  · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                    have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                    have hw4 : (18186303/400000000000:ℝ) ≤ wfun (y + z) := wc_156 (y + z) (by linarith) (by linarith)
                    have hw5 : (1629257293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_379 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (1626727581/10000000000000:ℝ) ≤ wfun y := wc_13 y (by linarith) (by linarith)
                    have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                    have hw4 : (259706701/1250000000000:ℝ) ≤ wfun (y + z) := wc_167 (y + z) (by linarith) (by linarith)
                    have hw5 : (5223624809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_383 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw3 : (4789633321/10000000000000:ℝ) ≤ wfun (x + y) := wc_172 (x + y) (by linarith) (by linarith)
                  have hw4 : (2001469121/10000000000000:ℝ) ≤ wfun (y + z) := wc_168 (y + z) (by linarith) (by linarith)
                  have hw5 : (5096134953/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_384 (x + y + z) (by linarith) (by linarith)
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
            have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw4 : (12244337/312500000000:ℝ) ≤ wfun (y + z) := wc_159 (y + z) (by linarith) (by linarith)
            have hw5 : (75856633/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_311 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
              rcases le_total x (1:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
            have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw4 : (129343671/312500000000:ℝ) ≤ wfun (y + z) := wc_175 (y + z) (by linarith) (by linarith)
            have hw5 : (1520846759/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_375 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (131/128:ℝ) with hc | hc
          · rcases le_total z (141/128:ℝ) with hc | hc
            · rcases le_total x (267/256:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw4 : (42177537/1000000000000:ℝ) ≤ wfun (y + z) := wc_158 (y + z) (by linarith) (by linarith)
                have hw5 : (1637121129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_373 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw4 : (42177537/1000000000000:ℝ) ≤ wfun (y + z) := wc_158 (y + z) (by linarith) (by linarith)
                have hw5 : (3100919687/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_381 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
              have hw4 : (1112362433/2500000000000:ℝ) ≤ wfun (y + z) := wc_174 (y + z) (by linarith) (by linarith)
              have hw5 : (37911123/78125000000:ℝ) ≤ wfun (x + y + z) := wc_385 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
            have hw4 : (129343671/312500000000:ℝ) ≤ wfun (y + z) := wc_175 (y + z) (by linarith) (by linarith)
            have hw5 : (589186081/1250000000000:ℝ) ≤ wfun (x + y + z) := by
              rcases le_total (x + y + z) (13/4:ℝ) with hq50 | hq50
              · exact le_trans (by norm_num) (wc_386 (x + y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_389 (x + y + z) (by linarith) (by linarith))
            linarith
    · rcases le_total z (17/16:ℝ) with hc | hc
      · rcases le_total x (131/128:ℝ) with hc | hc
        · rcases le_total y (141/128:ℝ) with hc | hc
          · rcases le_total z (131/128:ℝ) with hc | hc
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
              have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
                rcases le_total z (1:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
              have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
              have hw4 : (42177537/1000000000000:ℝ) ≤ wfun (y + z) := wc_158 (y + z) (by linarith) (by linarith)
              have hw5 : (79711817/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_310 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
              have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
              have hw4 : (1112362433/2500000000000:ℝ) ≤ wfun (y + z) := wc_174 (y + z) (by linarith) (by linarith)
              have hw5 : (798582451/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_374 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
              rcases le_total x (1:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
            have hw1 : (11778340313/10000000000000:ℝ) ≤ wfun y := wc_67 y (by linarith) (by linarith)
            have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
            have hw4 : (129343671/312500000000:ℝ) ≤ wfun (y + z) := wc_175 (y + z) (by linarith) (by linarith)
            have hw5 : (1520846759/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_375 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (141/128:ℝ) with hc | hc
          · rcases le_total z (131/128:ℝ) with hc | hc
            · have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
              have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
                rcases le_total z (1:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
              have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
              have hw4 : (42177537/1000000000000:ℝ) ≤ wfun (y + z) := wc_158 (y + z) (by linarith) (by linarith)
              have hw5 : (798582451/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_374 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (44604923/2500000000000:ℝ) ≤ wfun y := wc_62 y (by linarith) (by linarith)
              have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
              have hw4 : (1112362433/2500000000000:ℝ) ≤ wfun (y + z) := wc_174 (y + z) (by linarith) (by linarith)
              have hw5 : (37911123/78125000000:ℝ) ≤ wfun (x + y + z) := wc_385 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (11778340313/10000000000000:ℝ) ≤ wfun y := wc_67 y (by linarith) (by linarith)
            have hw3 : (48584483/40000000000:ℝ) ≤ wfun (x + y) := wc_178 (x + y) (by linarith) (by linarith)
            have hw4 : (129343671/312500000000:ℝ) ≤ wfun (y + z) := wc_175 (y + z) (by linarith) (by linarith)
            have hw5 : (589186081/1250000000000:ℝ) ≤ wfun (x + y + z) := by
              rcases le_total (x + y + z) (13/4:ℝ) with hq50 | hq50
              · exact le_trans (by norm_num) (wc_386 (x + y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_389 (x + y + z) (by linarith) (by linarith))
            linarith
      · have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
        have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
        have hw3 : (182240171/5000000000000:ℝ) ≤ wfun (x + y) := wc_160 (x + y) (by linarith) (by linarith)
        have hw4 : (2788858101/2500000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (9/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_179 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_182 (y + z) (by linarith) (by linarith))
        have hw5 : (589186081/1250000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (13/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_386 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_392 (x + y + z) (by linarith) (by linarith))
        linarith
  · rcases le_total y (17/16:ℝ) with hc | hc
    · rcases le_total z (17/16:ℝ) with hc | hc
      · rcases le_total x (141/128:ℝ) with hc | hc
        · rcases le_total y (131/128:ℝ) with hc | hc
          · rcases le_total z (131/128:ℝ) with hc | hc
            · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                rcases le_total y (1:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
              have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
                rcases le_total z (1:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
              have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
              have hw5 : (79711817/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_310 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (277/256:ℝ) with hc | hc
              · rcases le_total y (257/256:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (12267823741/5000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (1:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_6 y (by linarith) (by linarith))
                  have hw3 : (18186303/400000000000:ℝ) ≤ wfun (x + y) := wc_156 (x + y) (by linarith) (by linarith)
                  have hw5 : (419583999/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_372 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := wc_9 y (by linarith) (by linarith)
                  have hw3 : (259706701/1250000000000:ℝ) ≤ wfun (x + y) := wc_167 (x + y) (by linarith) (by linarith)
                  have hw5 : (1589247651/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_380 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (1:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
                have hw3 : (2001469121/10000000000000:ℝ) ≤ wfun (x + y) := wc_168 (x + y) (by linarith) (by linarith)
                have hw5 : (3100919687/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_381 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (131/128:ℝ) with hc | hc
            · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
                rcases le_total z (1:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
              have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
              have hw5 : (798582451/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_374 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
              have hw4 : (42177537/1000000000000:ℝ) ≤ wfun (y + z) := wc_158 (y + z) (by linarith) (by linarith)
              have hw5 : (37911123/78125000000:ℝ) ≤ wfun (x + y + z) := wc_385 (x + y + z) (by linarith) (by linarith)
              linarith
        · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
          have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_175 (x + y) (by linarith) (by linarith)
          have hw5 : (1477240831/10000000000000:ℝ) ≤ wfun (x + y + z) := by
            rcases le_total (x + y + z) (13/4:ℝ) with hq50 | hq50
            · exact le_trans (by norm_num) (wc_376 (x + y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_389 (x + y + z) (by linarith) (by linarith))
          linarith
      · rcases le_total x (141/128:ℝ) with hc | hc
        · rcases le_total y (131/128:ℝ) with hc | hc
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (2370342229/2500000000000:ℝ) ≤ wfun y := by
              rcases le_total y (1:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_5 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 y (by linarith) (by linarith))
            have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (42177537/1000000000000:ℝ) ≤ wfun (x + y) := wc_158 (x + y) (by linarith) (by linarith)
            have hw4 : (12244337/312500000000:ℝ) ≤ wfun (y + z) := wc_159 (y + z) (by linarith) (by linarith)
            have hw5 : (589186081/1250000000000:ℝ) ≤ wfun (x + y + z) := by
              rcases le_total (x + y + z) (13/4:ℝ) with hq50 | hq50
              · exact le_trans (by norm_num) (wc_386 (x + y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_389 (x + y + z) (by linarith) (by linarith))
            linarith
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (1112362433/2500000000000:ℝ) ≤ wfun (x + y) := wc_174 (x + y) (by linarith) (by linarith)
            have hw4 : (129343671/312500000000:ℝ) ≤ wfun (y + z) := wc_175 (y + z) (by linarith) (by linarith)
            have hw5 : (9713220361/10000000000000:ℝ) ≤ wfun (x + y + z) := by
              rcases le_total (x + y + z) (13/4:ℝ) with hq50 | hq50
              · exact le_trans (by norm_num) (wc_387 (x + y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_391 (x + y + z) (by linarith) (by linarith))
            linarith
        · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
          have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
          have hw3 : (129343671/312500000000:ℝ) ≤ wfun (x + y) := wc_175 (x + y) (by linarith) (by linarith)
          have hw4 : (182240171/5000000000000:ℝ) ≤ wfun (y + z) := wc_160 (y + z) (by linarith) (by linarith)
          have hw5 : (9713220361/10000000000000:ℝ) ≤ wfun (x + y + z) := by
            rcases le_total (x + y + z) (13/4:ℝ) with hq50 | hq50
            · exact le_trans (by norm_num) (wc_387 (x + y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_392 (x + y + z) (by linarith) (by linarith))
          linarith
    · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
      have hw1 : (15429929/1000000000000:ℝ) ≤ wfun y := wc_63 y (by linarith) (by linarith)
      have hw3 : (2788858101/2500000000000:ℝ) ≤ wfun (x + y) := by
        rcases le_total (x + y) (9/4:ℝ) with hq30 | hq30
        · exact le_trans (by norm_num) (wc_179 (x + y) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_182 (x + y) (by linarith) (by linarith))
      have hw4 : (167375901/5000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (9/4:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_161 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_182 (y + z) (by linarith) (by linarith))
      have hw5 : (589186081/1250000000000:ℝ) ≤ wfun (x + y + z) := by
        rcases le_total (x + y + z) (13/4:ℝ) with hq50 | hq50
        · exact le_trans (by norm_num) (wc_386 (x + y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_393 (x + y + z) (by linarith) (by linarith))
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_4 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (63/32:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (17/16:ℝ) with hc | hc
  · rcases le_total x (131/128:ℝ) with hc | hc
    · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
        rcases le_total x (1:ℝ) with hq00 | hq00
        · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
      have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_76 y (by linarith) (by linarith)
      have hw3 : (269743281/5000000000000:ℝ) ≤ wfun (x + y) := wc_188 (x + y) (by linarith) (by linarith)
      linarith
    · rcases le_total y (247/128:ℝ) with hc | hc
      · have hw1 : (9113139537/5000000000000:ℝ) ≤ wfun y := wc_75 y (by linarith) (by linarith)
        have hw3 : (288828359/5000000000000:ℝ) ≤ wfun (x + y) := wc_189 (x + y) (by linarith) (by linarith)
        have hw4 : (269743281/5000000000000:ℝ) ≤ wfun (y + z) := wc_188 (y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total z (131/128:ℝ) with hc | hc
        · have hw1 : (6731724963/10000000000000:ℝ) ≤ wfun y := wc_78 y (by linarith) (by linarith)
          have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
            rcases le_total z (1:ℝ) with hq20 | hq20
            · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
          have hw4 : (288828359/5000000000000:ℝ) ≤ wfun (y + z) := wc_189 (y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (267/256:ℝ) with hc | hc
          · rcases le_total y (499/256:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (6028900351/5000000000000:ℝ) ≤ wfun y := wc_77 y (by linarith) (by linarith)
              have hw3 : (15105971/250000000000:ℝ) ≤ wfun (x + y) := wc_197 (x + y) (by linarith) (by linarith)
              have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_198 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
              linarith
            · rcases le_total z (267/256:ℝ) with hc | hc
              · rcases le_total x (529/512:ℝ) with hc | hc
                · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                  have hw1 : (688065547/1000000000000:ℝ) ≤ wfun y := wc_80 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                  have hw3 : (13065663/500000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_208 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_218 (x + y) (by linarith) (by linarith))
                  have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_208 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                  linarith
                · rcases le_total y (1003/512:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                    have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                    have hw3 : (13065663/500000000000:ℝ) ≤ wfun (x + y) := by
                      rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                      · exact le_trans (by norm_num) (wc_213 (x + y) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_218 (x + y) (by linarith) (by linarith))
                    have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_208 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_218 (y + z) (by linarith) (by linarith))
                    linarith
                  · rcases le_total z (529/512:ℝ) with hc | hc
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                      have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                      have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                        rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                        · exact le_trans (by norm_num) (wc_215 (x + y) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
                      have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_213 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_218 (y + z) (by linarith) (by linarith))
                      have hw5 : (31777/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_452 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                      have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                      have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                        rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                        · exact le_trans (by norm_num) (wc_215 (x + y) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
                      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                      have hw5 : (10750333/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_492 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total x (529/512:ℝ) with hc | hc
                · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                  have hw1 : (688065547/1000000000000:ℝ) ≤ wfun y := wc_80 y (by linarith) (by linarith)
                  have hw3 : (13065663/500000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_208 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_218 (x + y) (by linarith) (by linarith))
                  have hw5 : (31169/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_454 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (1003/512:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                    have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                    have hw3 : (13065663/500000000000:ℝ) ≤ wfun (x + y) := by
                      rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                      · exact le_trans (by norm_num) (wc_213 (x + y) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_218 (x + y) (by linarith) (by linarith))
                    have hw5 : (1064707/250000000000:ℝ) ≤ wfun (x + y + z) := wc_493 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total z (539/512:ℝ) with hc | hc
                    · rcases le_total x (1063/1024:ℝ) with hc | hc
                      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                        have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                        have hw3 : (70009749/5000000000000:ℝ) ≤ wfun (x + y) := by
                          rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                          · exact le_trans (by norm_num) (wc_215 (x + y) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_219 (x + y) (by linarith) (by linarith))
                        have hw5 : (165310021/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_508 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                          have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                          have hw3 : (70009749/5000000000000:ℝ) ≤ wfun (x + y) := by
                            rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                            · exact le_trans (by norm_num) (wc_217 (x + y) (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_219 (x + y) (by linarith) (by linarith))
                          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_224 (y + z) (by linarith) (by linarith)
                          have hw5 : (128356097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_520 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · rcases le_total z (1073/1024:ℝ) with hc | hc
                          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                            have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                            have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_223 (x + y) (by linarith) (by linarith)
                            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
                            have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_527 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · rcases le_total x (2131/2048:ℝ) with hc | hc
                            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_20 x (by linarith) (by linarith)
                              have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                              have hw3 : (93531111/10000000000000:ℝ) ≤ wfun (x + y) := wc_222 (x + y) (by linarith) (by linarith)
                              have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_536 (x + y + z) (by linarith) (by linarith)
                              linarith
                            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                              have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                              have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_225 (x + y) (by linarith) (by linarith)
                              have hw5 : (570814473/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_541 (x + y + z) (by linarith) (by linarith)
                              linarith
                    · rcases le_total x (1063/1024:ℝ) with hc | hc
                      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                        have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                        have hw3 : (70009749/5000000000000:ℝ) ≤ wfun (x + y) := by
                          rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                          · exact le_trans (by norm_num) (wc_215 (x + y) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_219 (x + y) (by linarith) (by linarith))
                        have hw5 : (182379599/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_529 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                          have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                          have hw3 : (70009749/5000000000000:ℝ) ≤ wfun (x + y) := by
                            rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                            · exact le_trans (by norm_num) (wc_217 (x + y) (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_219 (x + y) (by linarith) (by linarith))
                          have hw5 : (495290917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_538 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                          have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                          have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_223 (x + y) (by linarith) (by linarith)
                          have hw5 : (160690591/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_546 (x + y + z) (by linarith) (by linarith)
                          linarith
          · rcases le_total y (499/256:ℝ) with hc | hc
            · have hw1 : (6028900351/5000000000000:ℝ) ≤ wfun y := wc_77 y (by linarith) (by linarith)
              have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_208 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
              have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_198 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
              linarith
            · rcases le_total z (267/256:ℝ) with hc | hc
              · rcases le_total x (539/512:ℝ) with hc | hc
                · rcases le_total y (1003/512:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                    have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                      rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                      · exact le_trans (by norm_num) (wc_215 (x + y) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
                    have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_208 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_218 (y + z) (by linarith) (by linarith))
                    have hw5 : (31471/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_453 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total z (529/512:ℝ) with hc | hc
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                      have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                      have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_213 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_218 (y + z) (by linarith) (by linarith))
                      have hw5 : (10750333/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_492 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total x (1073/1024:ℝ) with hc | hc
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                          have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                          have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_223 (x + y) (by linarith) (by linarith)
                          have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                            rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                            · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_219 (y + z) (by linarith) (by linarith))
                          have hw5 : (8305511/500000000000:ℝ) ≤ wfun (x + y + z) := wc_507 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · rcases le_total z (1063/1024:ℝ) with hc | hc
                          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                            have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
                            have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                              rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                              · exact le_trans (by norm_num) (wc_217 (y + z) (by linarith) (by linarith))
                              exact le_trans (by norm_num) (wc_219 (y + z) (by linarith) (by linarith))
                            have hw5 : (128977417/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_519 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                            have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
                            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
                            have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_527 (x + y + z) (by linarith) (by linarith)
                            linarith
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
                          have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                            rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                            · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_219 (y + z) (by linarith) (by linarith))
                          have hw5 : (128356097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_520 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · rcases le_total z (1063/1024:ℝ) with hc | hc
                          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                            have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                            have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                              rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                              · exact le_trans (by norm_num) (wc_217 (y + z) (by linarith) (by linarith))
                              exact le_trans (by norm_num) (wc_219 (y + z) (by linarith) (by linarith))
                            have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_527 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · rcases le_total x (2151/2048:ℝ) with hc | hc
                            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                              have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_232 (x + y) (by linarith) (by linarith)
                              have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
                              have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_536 (x + y + z) (by linarith) (by linarith)
                              linarith
                            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                              have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                              have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
                              have hw5 : (570814473/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_541 (x + y + z) (by linarith) (by linarith)
                              linarith
                · rcases le_total y (1003/512:ℝ) with hc | hc
                  · have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                    have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_208 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_218 (y + z) (by linarith) (by linarith))
                    have hw5 : (1064707/250000000000:ℝ) ≤ wfun (x + y + z) := wc_493 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total z (529/512:ℝ) with hc | hc
                    · have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                      have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_213 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_218 (y + z) (by linarith) (by linarith))
                      have hw5 : (164514637/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_509 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total x (1083/1024:ℝ) with hc | hc
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                          have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                            rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                            · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_219 (y + z) (by linarith) (by linarith))
                          have hw5 : (183260287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_528 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · rcases le_total z (1063/1024:ℝ) with hc | hc
                          · have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_16 z (by linarith) (by linarith)
                            have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                              rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                              · exact le_trans (by norm_num) (wc_217 (y + z) (by linarith) (by linarith))
                              exact le_trans (by norm_num) (wc_219 (y + z) (by linarith) (by linarith))
                            have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_537 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
                            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
                            have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_545 (x + y + z) (by linarith) (by linarith)
                            linarith
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                          have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                          have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                            rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                            · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_219 (y + z) (by linarith) (by linarith))
                          have hw5 : (495290917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_538 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                          have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                          have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
                          have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                            rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                            · exact le_trans (by norm_num) (wc_217 (y + z) (by linarith) (by linarith))
                            exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                          have hw5 : (160690591/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_546 (x + y + z) (by linarith) (by linarith)
                          linarith
              · rcases le_total x (539/512:ℝ) with hc | hc
                · rcases le_total y (1003/512:ℝ) with hc | hc
                  · rcases le_total z (539/512:ℝ) with hc | hc
                    · rcases le_total x (1073/1024:ℝ) with hc | hc
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                        have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                        have hw3 : (70009749/5000000000000:ℝ) ≤ wfun (x + y) := by
                          rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                          · exact le_trans (by norm_num) (wc_215 (x + y) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_219 (x + y) (by linarith) (by linarith))
                        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                        have hw5 : (165310021/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_508 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                        have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                        have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                          rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                          · exact le_trans (by norm_num) (wc_217 (x + y) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
                        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_215 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_221 (y + z) (by linarith) (by linarith))
                        have hw5 : (255477031/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_521 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                      have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                      have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                        rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                        · exact le_trans (by norm_num) (wc_215 (x + y) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
                      have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_530 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total z (539/512:ℝ) with hc | hc
                    · rcases le_total x (1073/1024:ℝ) with hc | hc
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · rcases le_total z (1073/1024:ℝ) with hc | hc
                          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                            have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                            have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_223 (x + y) (by linarith) (by linarith)
                            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
                            have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_527 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                            have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                            have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_223 (x + y) (by linarith) (by linarith)
                            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
                            have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_537 (x + y + z) (by linarith) (by linarith)
                            linarith
                        · rcases le_total z (1073/1024:ℝ) with hc | hc
                          · rcases le_total x (2141/2048:ℝ) with hc | hc
                            · rcases le_total y (4027/2048:ℝ) with hc | hc
                              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                                have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_83 y (by linarith) (by linarith)
                                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                                have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_226 (x + y) (by linarith) (by linarith)
                                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
                                have hw5 : (20003551/400000000000:ℝ) ≤ wfun (x + y + z) := wc_535 (x + y + z) (by linarith) (by linarith)
                                linarith
                              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                                have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                                have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_229 (x + y) (by linarith) (by linarith)
                                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_230 (y + z) (by linarith) (by linarith)
                                have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_540 (x + y + z) (by linarith) (by linarith)
                                linarith
                            · rcases le_total y (4027/2048:ℝ) with hc | hc
                              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                                have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_83 y (by linarith) (by linarith)
                                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                                have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_229 (x + y) (by linarith) (by linarith)
                                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
                                have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_540 (x + y + z) (by linarith) (by linarith)
                                linarith
                              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                                have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_230 (y + z) (by linarith) (by linarith)
                                have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_543 (x + y + z) (by linarith) (by linarith)
                                linarith
                          · rcases le_total x (2141/2048:ℝ) with hc | hc
                            · rcases le_total y (4027/2048:ℝ) with hc | hc
                              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                                have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_83 y (by linarith) (by linarith)
                                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                                have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_226 (x + y) (by linarith) (by linarith)
                                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
                                have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_543 (x + y + z) (by linarith) (by linarith)
                                linarith
                              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                                have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                                have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_229 (x + y) (by linarith) (by linarith)
                                have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_558 (x + y + z) (by linarith) (by linarith)
                                linarith
                            · rcases le_total y (4027/2048:ℝ) with hc | hc
                              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                                have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_83 y (by linarith) (by linarith)
                                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                                have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_229 (x + y) (by linarith) (by linarith)
                                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
                                have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_558 (x + y + z) (by linarith) (by linarith)
                                linarith
                              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                                have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                                have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_561 (x + y + z) (by linarith) (by linarith)
                                linarith
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · rcases le_total z (1073/1024:ℝ) with hc | hc
                          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                            have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
                            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
                            have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_537 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                            have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
                            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
                            have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_545 (x + y + z) (by linarith) (by linarith)
                            linarith
                        · rcases le_total z (1073/1024:ℝ) with hc | hc
                          · rcases le_total x (2151/2048:ℝ) with hc | hc
                            · rcases le_total y (4027/2048:ℝ) with hc | hc
                              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                                have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_83 y (by linarith) (by linarith)
                                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
                                have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_543 (x + y + z) (by linarith) (by linarith)
                                linarith
                              · rcases le_total z (2141/2048:ℝ) with hc | hc
                                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                                  have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                                  have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_229 (y + z) (by linarith) (by linarith)
                                  have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_557 (x + y + z) (by linarith) (by linarith)
                                  linarith
                                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                                  have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                                  have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
                                  have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
                                  linarith
                            · rcases le_total y (4027/2048:ℝ) with hc | hc
                              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                                have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_83 y (by linarith) (by linarith)
                                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
                                have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_558 (x + y + z) (by linarith) (by linarith)
                                linarith
                              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                                have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_230 (y + z) (by linarith) (by linarith)
                                have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_561 (x + y + z) (by linarith) (by linarith)
                                linarith
                          · rcases le_total x (2151/2048:ℝ) with hc | hc
                            · rcases le_total y (4027/2048:ℝ) with hc | hc
                              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                                have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_83 y (by linarith) (by linarith)
                                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_231 (x + y) (by linarith) (by linarith)
                                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
                                have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_561 (x + y + z) (by linarith) (by linarith)
                                linarith
                              · rcases le_total z (2151/2048:ℝ) with hc | hc
                                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                                  have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                                  have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
                                  linarith
                                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                                  have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                                  have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                                  have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
                                  linarith
                            · rcases le_total y (4027/2048:ℝ) with hc | hc
                              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                                have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_83 y (by linarith) (by linarith)
                                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                                have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_234 (x + y) (by linarith) (by linarith)
                                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
                                have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_572 (x + y + z) (by linarith) (by linarith)
                                linarith
                              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                                have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                                have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_582 (x + y + z) (by linarith) (by linarith)
                                linarith
                    · rcases le_total x (1073/1024:ℝ) with hc | hc
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                          have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                          have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_223 (x + y) (by linarith) (by linarith)
                          have hw5 : (160690591/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_546 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · rcases le_total z (1083/1024:ℝ) with hc | hc
                          · rcases le_total x (2141/2048:ℝ) with hc | hc
                            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                              have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                              have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_227 (x + y) (by linarith) (by linarith)
                              have hw5 : (407254991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_562 (x + y + z) (by linarith) (by linarith)
                              linarith
                            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                              have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                              have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_230 (x + y) (by linarith) (by linarith)
                              have hw5 : (45246083/500000000000:ℝ) ≤ wfun (x + y + z) := wc_573 (x + y + z) (by linarith) (by linarith)
                              linarith
                          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                            have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
                            have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
                            have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_584 (x + y + z) (by linarith) (by linarith)
                            linarith
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_228 (x + y) (by linarith) (by linarith)
                          have hw5 : (808657969/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_564 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · rcases le_total z (1083/1024:ℝ) with hc | hc
                          · rcases le_total x (2151/2048:ℝ) with hc | hc
                            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                              have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_232 (x + y) (by linarith) (by linarith)
                              have hw5 : (199972023/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_583 (x + y + z) (by linarith) (by linarith)
                              linarith
                            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                              have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                              have hw5 : (549643007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_599 (x + y + z) (by linarith) (by linarith)
                              linarith
                          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                            have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                            have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
                            have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_613 (x + y + z) (by linarith) (by linarith)
                            linarith
                · rcases le_total y (1003/512:ℝ) with hc | hc
                  · have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                    have hw5 : (89884553/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_531 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total z (539/512:ℝ) with hc | hc
                    · rcases le_total x (1083/1024:ℝ) with hc | hc
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · rcases le_total z (1073/1024:ℝ) with hc | hc
                          · have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_223 (y + z) (by linarith) (by linarith)
                            have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_545 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
                            have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_563 (x + y + z) (by linarith) (by linarith)
                            linarith
                        · rcases le_total z (1073/1024:ℝ) with hc | hc
                          · rcases le_total x (2161/2048:ℝ) with hc | hc
                            · rcases le_total y (4027/2048:ℝ) with hc | hc
                              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                                have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_83 y (by linarith) (by linarith)
                                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                                have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_227 (y + z) (by linarith) (by linarith)
                                have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_561 (x + y + z) (by linarith) (by linarith)
                                linarith
                              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                                have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_230 (y + z) (by linarith) (by linarith)
                                have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_572 (x + y + z) (by linarith) (by linarith)
                                linarith
                            · have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
                              have hw5 : (45246083/500000000000:ℝ) ≤ wfun (x + y + z) := wc_573 (x + y + z) (by linarith) (by linarith)
                              linarith
                          · rcases le_total x (2161/2048:ℝ) with hc | hc
                            · rcases le_total y (4027/2048:ℝ) with hc | hc
                              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                                have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_83 y (by linarith) (by linarith)
                                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
                                have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_582 (x + y + z) (by linarith) (by linarith)
                                linarith
                              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                                have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_85 y (by linarith) (by linarith)
                                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                                have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_598 (x + y + z) (by linarith) (by linarith)
                                linarith
                            · have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                              have hw5 : (549643007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_599 (x + y + z) (by linarith) (by linarith)
                              linarith
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                          have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_224 (y + z) (by linarith) (by linarith)
                          have hw5 : (808657969/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_564 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · rcases le_total z (1073/1024:ℝ) with hc | hc
                          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                            have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                            have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
                            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
                            have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_584 (x + y + z) (by linarith) (by linarith)
                            linarith
                          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                            have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                            have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
                            have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_613 (x + y + z) (by linarith) (by linarith)
                            linarith
                    · rcases le_total x (1083/1024:ℝ) with hc | hc
                      · rcases le_total y (2011/1024:ℝ) with hc | hc
                        · have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_81 y (by linarith) (by linarith)
                          have hw5 : (198537007/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_585 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_84 y (by linarith) (by linarith)
                          have hw5 : (37329233/312500000000:ℝ) ≤ wfun (x + y + z) := wc_614 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                        have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                        have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_615 (x + y + z) (by linarith) (by linarith)
                        linarith
  · rcases le_total x (131/128:ℝ) with hc | hc
    · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
        rcases le_total x (1:ℝ) with hq00 | hq00
        · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
      have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_76 y (by linarith) (by linarith)
      have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
      have hw3 : (269743281/5000000000000:ℝ) ≤ wfun (x + y) := wc_188 (x + y) (by linarith) (by linarith)
      linarith
    · rcases le_total y (247/128:ℝ) with hc | hc
      · have hw1 : (9113139537/5000000000000:ℝ) ≤ wfun y := wc_75 y (by linarith) (by linarith)
        have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
        have hw3 : (288828359/5000000000000:ℝ) ≤ wfun (x + y) := wc_189 (x + y) (by linarith) (by linarith)
        linarith
      · rcases le_total z (141/128:ℝ) with hc | hc
        · rcases le_total x (267/256:ℝ) with hc | hc
          · rcases le_total y (499/256:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (6028900351/5000000000000:ℝ) ≤ wfun y := wc_77 y (by linarith) (by linarith)
              have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (15105971/250000000000:ℝ) ≤ wfun (x + y) := wc_197 (x + y) (by linarith) (by linarith)
              have hw5 : (60567/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_456 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (277/256:ℝ) with hc | hc
              · rcases le_total x (529/512:ℝ) with hc | hc
                · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                  have hw1 : (688065547/1000000000000:ℝ) ≤ wfun y := wc_80 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw3 : (13065663/500000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_208 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_218 (x + y) (by linarith) (by linarith))
                  have hw5 : (20172571/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_511 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (1003/512:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                    have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                    have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                    have hw3 : (13065663/500000000000:ℝ) ≤ wfun (x + y) := by
                      rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                      · exact le_trans (by norm_num) (wc_213 (x + y) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_218 (x + y) (by linarith) (by linarith))
                    have hw5 : (89884553/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_531 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                    have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                    have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                    have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                      rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                      · exact le_trans (by norm_num) (wc_215 (x + y) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
                    have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_247 (y + z) (by linarith) (by linarith)
                    have hw5 : (315273331/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_549 (x + y + z) (by linarith) (by linarith)
                    linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                have hw1 : (688065547/1000000000000:ℝ) ≤ wfun y := wc_80 y (by linarith) (by linarith)
                have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                  rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                  · exact le_trans (by norm_num) (wc_208 (x + y) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
                have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                have hw5 : (154654989/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_551 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (499/256:ℝ) with hc | hc
            · have hw1 : (6028900351/5000000000000:ℝ) ≤ wfun y := wc_77 y (by linarith) (by linarith)
              have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_208 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
              have hw5 : (39204539/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_513 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (277/256:ℝ) with hc | hc
              · rcases le_total x (539/512:ℝ) with hc | hc
                · rcases le_total y (1003/512:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                    have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                    have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                      rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                      · exact le_trans (by norm_num) (wc_215 (x + y) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
                    have hw5 : (315273331/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_549 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total z (549/512:ℝ) with hc | hc
                    · rcases le_total x (1073/1024:ℝ) with hc | hc
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                        have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                        have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_224 (x + y) (by linarith) (by linarith)
                        have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                        have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_586 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                        have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                        have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_246 (y + z) (by linarith) (by linarith)
                        have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_615 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                      have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                      have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                      have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                      have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_654 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (1003/512:ℝ) with hc | hc
                  · have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_79 y (by linarith) (by linarith)
                    have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                    have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_588 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_82 y (by linarith) (by linarith)
                    have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                    have hw4 : (285997/2500000000000:ℝ) ≤ wfun (y + z) := wc_247 (y + z) (by linarith) (by linarith)
                    have hw5 : (69357131/500000000000:ℝ) ≤ wfun (x + y + z) := wc_655 (x + y + z) (by linarith) (by linarith)
                    linarith
              · have hw1 : (688065547/1000000000000:ℝ) ≤ wfun y := wc_80 y (by linarith) (by linarith)
                have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw4 : (88186617/10000000000000:ℝ) ≤ wfun (y + z) := wc_306 (y + z) (by linarith) (by linarith)
                have hw5 : (1361028853/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_657 (x + y + z) (by linarith) (by linarith)
                linarith
        · have hw1 : (6731724963/10000000000000:ℝ) ≤ wfun y := wc_78 y (by linarith) (by linarith)
          have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
          have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
          have hw5 : (913271/15625000000:ℝ) ≤ wfun (x + y + z) := wc_554 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_53 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (131/128:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (63/32:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
lemma ch_56 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (257/128:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (63/32:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
          have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
          linarith
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
              rcases le_total z (2:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
            have hw3 : (22330933/2500000000000:ℝ) ≤ wfun (x + y) := wc_305 (x + y) (by linarith) (by linarith)
            have hw5 : (14162149/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_770 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1023/512:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                have hw5 : (38980307/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_787 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_343 (x + y) (by linarith) (by linarith)
                  have hw5 : (19225319/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_806 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                    have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                    have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_828 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                    have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (1023/512:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                have hw5 : (191511939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_807 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (509/256:ℝ) with hc | hc
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
          have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_771 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
              rcases le_total z (2:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
            have hw3 : (676941261/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
            have hw5 : (37716487/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_809 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
              rcases le_total z (2:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
            have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_366 (x + y) (by linarith) (by linarith)
            have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
            have hw5 : (43578037/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (519/256:ℝ) with hc | hc
      · rcases le_total z (509/256:ℝ) with hc | hc
        · rcases le_total x (539/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
              have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
              have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_419 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
              have hw5 : (3568011/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_769 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
              have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
              have hw5 : (38680157/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_788 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
            have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_366 (x + y) (by linarith) (by linarith)
            have hw5 : (76765783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_789 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (539/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1023/512:ℝ) with hc | hc
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                  have hw3 : (172511147/2500000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                  have hw5 : (19225319/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_806 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                  have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                  have hw5 : (26775111/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_830 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (2051/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                      have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 z (by linarith) (by linarith))
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                      have hw5 : (358152183/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                      have hw5 : (458561277/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
                    have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
                    have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (9367789/78125000000:ℝ) ≤ wfun (x + y) := wc_364 (x + y) (by linarith) (by linarith)
                    have hw5 : (568693187/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_878 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total z (1023/512:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_880 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1023/512:ℝ) with hc | hc
              · have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                have hw5 : (354029429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_880 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
              have hw3 : (1810022563/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
              have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (509/256:ℝ) with hc | hc
        · have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
          have hw5 : (187138697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_810 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
            rcases le_total z (2:ℝ) with hq20 | hq20
            · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
          have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
          have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
          have hw5 : (551493311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total x (267/256:ℝ) with hc | hc
    · rcases le_total y (519/256:ℝ) with hc | hc
      · rcases le_total z (519/256:ℝ) with hc | hc
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
            have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
            have hw3 : (22330933/2500000000000:ℝ) ≤ wfun (x + y) := wc_305 (x + y) (by linarith) (by linarith)
            have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
            have hw5 : (37716487/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_809 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1033/512:ℝ) with hc | hc
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                  have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_343 (x + y) (by linarith) (by linarith)
                  have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_451 (y + z) (by linarith) (by linarith)
                  have hw5 : (71079411/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_844 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                    have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                    have hw4 : (32243/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                    have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                    have hw4 : (11791793/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                    have hw5 : (568693187/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_878 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (1063/1024:ℝ) with hc | hc
                · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_343 (x + y) (by linarith) (by linarith)
                  have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
                  have hw5 : (566506871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_879 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                  have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
                  have hw5 : (68963139/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
              have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
              have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
              have hw4 : (10750333/2500000000000:ℝ) ≤ wfun (y + z) := wc_492 (y + z) (by linarith) (by linarith)
              have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (529/512:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
            have hw3 : (22330933/2500000000000:ℝ) ≤ wfun (x + y) := wc_305 (x + y) (by linarith) (by linarith)
            have hw4 : (81469089/5000000000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
            have hw5 : (69466449/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_882 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
            have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
            have hw4 : (81469089/5000000000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
            have hw5 : (404289107/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
        have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
        have hw4 : (159841537/10000000000000:ℝ) ≤ wfun (y + z) := wc_512 (y + z) (by linarith) (by linarith)
        have hw5 : (108627463/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total y (519/256:ℝ) with hc | hc
      · rcases le_total z (519/256:ℝ) with hc | hc
        · rcases le_total x (539/512:ℝ) with hc | hc
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · rcases le_total z (1033/512:ℝ) with hc | hc
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · rcases le_total z (2061/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                      have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_144 z (by linarith) (by linarith)
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                      have hw4 : (64801/10000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
                      have hw5 : (114178013/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                      have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_147 z (by linarith) (by linarith)
                      have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                      have hw4 : (11849221/10000000000000:ℝ) ≤ wfun (y + z) := wc_475 (y + z) (by linarith) (by linarith)
                      have hw5 : (694962061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_901 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                    have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
                    have hw4 : (11791793/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                    have hw5 : (692290309/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (2061/1024:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (543159341/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                    have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
                    have hw4 : (32243/5000000000000:ℝ) ≤ wfun (y + z) := wc_450 (y + z) (by linarith) (by linarith)
                    have hw5 : (692290309/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_145 z (by linarith) (by linarith)
                    have hw3 : (9367789/78125000000:ℝ) ≤ wfun (x + y) := wc_364 (x + y) (by linarith) (by linarith)
                    have hw4 : (11791793/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                    have hw5 : (827400419/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (1073/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (172511147/2500000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                  have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
                  have hw5 : (824225629/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                  have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_149 z (by linarith) (by linarith)
                  have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                  have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_491 (y + z) (by linarith) (by linarith)
                  have hw5 : (194018909/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
              have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
              have hw4 : (10750333/2500000000000:ℝ) ≤ wfun (y + z) := wc_492 (y + z) (by linarith) (by linarith)
              have hw5 : (814792219/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (1033/512:ℝ) with hc | hc
            · have hw1 : (27945219/1000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
              have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
              have hw4 : (31777/5000000000000:ℝ) ≤ wfun (y + z) := wc_452 (y + z) (by linarith) (by linarith)
              have hw5 : (814792219/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
              have hw3 : (1810022563/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
              have hw4 : (10750333/2500000000000:ℝ) ≤ wfun (y + z) := wc_492 (y + z) (by linarith) (by linarith)
              have hw5 : (1114158849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
              linarith
        · have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
          have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
          have hw4 : (81469089/5000000000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
          have hw5 : (1097277581/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
        have hw4 : (159841537/10000000000000:ℝ) ≤ wfun (y + z) := wc_512 (y + z) (by linarith) (by linarith)
        have hw5 : (270178737/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_948 (x + y + z) (by linarith) (by linarith)
        linarith

end Zeta23Ext.Bridge.FourPoint
