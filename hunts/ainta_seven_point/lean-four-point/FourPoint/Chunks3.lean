import FourPoint.Cells

/-! Chunk module 3 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_3 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (237/64:ℝ) ≤ z) (hz2 : z ≤ (233/40:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (3049/640:ℝ) with hc | hc
  · rcases le_total z (5419/1280:ℝ) with hc | hc
    · rcases le_total z (10159/2560:ℝ) with hc | hc
      · rcases le_total z (19639/5120:ℝ) with hc | hc
        · have hw2 : (6366839399/5000000000000:ℝ) ≤ wfun z := by
            rcases le_total z (15/4:ℝ) with hq20 | hq20
            · exact le_trans (by norm_num) (wc_623 z (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_624 z (by linarith) (by linarith))
          have hw4 : (270897677/10000000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (19/4:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_1208 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_1210 (y + z) (by linarith) (by linarith))
          linarith
        · have hw2 : (8453897/100000000000:ℝ) ≤ wfun z := wc_625 z (by linarith) (by linarith)
          linarith
      · linarith
    · linarith
  · linarith

set_option maxHeartbeats 20000000 in
lemma ch_5 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (247/128:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  have hw1 : (9113139537/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
  have hw3 : (288828359/5000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
  have hw4 : (269743281/5000000000000:ℝ) ≤ wfun (y + z) := wc_288 (y + z) (by linarith) (by linarith)
  linarith

set_option maxHeartbeats 20000000 in
lemma ch_8 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (247/128:ℝ) ≤ y) (hy2 : y ≤ (63/32:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (499/256:ℝ) with hc | hc
  · have hw1 : (6028900351/5000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
    have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
      rcases le_total (x + y) (3:ℝ) with hq30 | hq30
      · exact le_trans (by norm_num) (wc_312 (x + y) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_327 (x + y) (by linarith) (by linarith))
    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
      rcases le_total (y + z) (3:ℝ) with hq40 | hq40
      · exact le_trans (by norm_num) (wc_302 (y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
    linarith
  · rcases le_total z (267/256:ℝ) with hc | hc
    · rcases le_total x (539/512:ℝ) with hc | hc
      · rcases le_total y (1003/512:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
          have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
          have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
            rcases le_total (x + y) (3:ℝ) with hq30 | hq30
            · exact le_trans (by norm_num) (wc_321 (x + y) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_327 (x + y) (by linarith) (by linarith))
          have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (3:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_312 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_324 (y + z) (by linarith) (by linarith))
          have hw5 : (31471/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (529/512:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
            have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
            have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (3:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_319 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_324 (y + z) (by linarith) (by linarith))
            have hw5 : (10750333/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_759 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (1073/1024:ℝ) with hc | hc
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
                have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_321 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_325 (y + z) (by linarith) (by linarith))
                have hw5 : (8305511/500000000000:ℝ) ≤ wfun (x + y + z) := wc_781 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (1063/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                  have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
                  have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_323 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_325 (y + z) (by linarith) (by linarith))
                  have hw5 : (128977417/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (2141/2048:ℝ) with hc | hc
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                    have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                    have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                    have hw5 : (184591317/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_801 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                    have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                    have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_337 (x + y) (by linarith) (by linarith)
                    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                    have hw5 : (431662129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_810 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
                have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_321 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_325 (y + z) (by linarith) (by linarith))
                have hw5 : (128356097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_795 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (1063/1024:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                  have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                  have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_323 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_325 (y + z) (by linarith) (by linarith))
                  have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_802 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (2151/2048:ℝ) with hc | hc
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                      have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
                      have hw4 : (93531111/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
                      have hw5 : (20003551/400000000000:ℝ) ≤ wfun (x + y + z) := wc_811 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                      have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                      have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_332 (y + z) (by linarith) (by linarith)
                      have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_817 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                      have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                      have hw4 : (93531111/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
                      have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_817 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                      have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                      have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_332 (y + z) (by linarith) (by linarith)
                      have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_821 (x + y + z) (by linarith) (by linarith)
                      linarith
      · rcases le_total y (1003/512:ℝ) with hc | hc
        · have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
          have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (3:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_312 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_324 (y + z) (by linarith) (by linarith))
          have hw5 : (1064707/250000000000:ℝ) ≤ wfun (x + y + z) := wc_760 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (529/512:ℝ) with hc | hc
          · have hw1 : (694601603/1000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
            have hw4 : (13065663/500000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (3:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_319 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_324 (y + z) (by linarith) (by linarith))
            have hw5 : (164514637/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_783 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (1083/1024:ℝ) with hc | hc
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_321 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_325 (y + z) (by linarith) (by linarith))
                have hw5 : (183260287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_803 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (1063/1024:ℝ) with hc | hc
                · have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                  have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_323 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_325 (y + z) (by linarith) (by linarith))
                  have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_813 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                  have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_823 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
                have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_321 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_325 (y + z) (by linarith) (by linarith))
                have hw5 : (495290917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_814 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (1063/1024:ℝ) with hc | hc
                · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
                  have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
                  have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                  have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_323 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_325 (y + z) (by linarith) (by linarith))
                  have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_823 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
                  have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
                  have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                  have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                  have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_850 (x + y + z) (by linarith) (by linarith)
                  linarith
    · rcases le_total x (539/512:ℝ) with hc | hc
      · rcases le_total y (1003/512:ℝ) with hc | hc
        · rcases le_total z (539/512:ℝ) with hc | hc
          · rcases le_total x (1073/1024:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
              have hw3 : (70009749/5000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_321 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_325 (x + y) (by linarith) (by linarith))
              have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_321 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
              have hw5 : (165310021/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_782 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (2001/1024:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                have hw1 : (10794742611/10000000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                have hw3 : (70009749/5000000000000:ℝ) ≤ wfun (x + y) := by
                  rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                  · exact le_trans (by norm_num) (wc_323 (x + y) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_325 (x + y) (by linarith) (by linarith))
                have hw4 : (70009749/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_321 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_325 (y + z) (by linarith) (by linarith))
                have hw5 : (128356097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_795 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                have hw1 : (4713649797/5000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
                have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (3:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_323 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
                have hw5 : (183260287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_803 (x + y + z) (by linarith) (by linarith)
                linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
            have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
            have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
              rcases le_total (x + y) (3:ℝ) with hq30 | hq30
              · exact le_trans (by norm_num) (wc_321 (x + y) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_327 (x + y) (by linarith) (by linarith))
            have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (539/512:ℝ) with hc | hc
          · rcases le_total x (1073/1024:ℝ) with hc | hc
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · rcases le_total z (1073/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
                  have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                  have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_802 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (2141/2048:ℝ) with hc | hc
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                    have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                    have hw3 : (93531111/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                    have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
                    have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_812 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                    have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                    have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_332 (x + y) (by linarith) (by linarith)
                    have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
                    have hw5 : (570814473/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_818 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (1073/1024:ℝ) with hc | hc
                · rcases le_total x (2141/2048:ℝ) with hc | hc
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                      have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_333 (x + y) (by linarith) (by linarith)
                      have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                      have hw5 : (20003551/400000000000:ℝ) ≤ wfun (x + y + z) := wc_811 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                      · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                        have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_336 (x + y) (by linarith) (by linarith)
                        have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
                        have hw5 : (573574207/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_816 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                        have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_336 (x + y) (by linarith) (by linarith)
                        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
                        have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                      have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_336 (x + y) (by linarith) (by linarith)
                      have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                      have hw5 : (572192259/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_817 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                        have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
                        have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
                        have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                        have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
                        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
                        have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
                        linarith
                · rcases le_total x (2141/2048:ℝ) with hc | hc
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                      have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_333 (x + y) (by linarith) (by linarith)
                      have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                      have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_821 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                      · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                        have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_336 (x + y) (by linarith) (by linarith)
                        have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                        have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                        have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_336 (x + y) (by linarith) (by linarith)
                        have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                      have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_336 (x + y) (by linarith) (by linarith)
                      have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                      have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                      · rcases le_total x (4287/4096:ℝ) with hc | hc
                        · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                          have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                          have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                          have hw3 : (18318183/10000000000000:ℝ) ≤ wfun (x + y) := wc_338 (x + y) (by linarith) (by linarith)
                          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                          have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
                          have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                          have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                          have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_856 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                        have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
                        have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                        linarith
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · rcases le_total z (1073/1024:ℝ) with hc | hc
                · rcases le_total x (2151/2048:ℝ) with hc | hc
                  · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                    have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                    have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                    have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_812 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                    have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                    have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_337 (x + y) (by linarith) (by linarith)
                    have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                    have hw5 : (570814473/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_818 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (2151/2048:ℝ) with hc | hc
                  · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                    have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                    have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                    have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
                    have hw5 : (323709737/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_822 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                    have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                    have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_337 (x + y) (by linarith) (by linarith)
                    have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
                    have hw5 : (728663451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_841 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (1073/1024:ℝ) with hc | hc
                · rcases le_total x (2151/2048:ℝ) with hc | hc
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                      have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
                      have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                      have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_821 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                      · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                        have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                        have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
                        have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total x (4297/4096:ℝ) with hc | hc
                        · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                          have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                          have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
                          have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                          have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
                          have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_856 (x + y + z) (by linarith) (by linarith)
                          linarith
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                      have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                      have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                      have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                        have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
                        have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
                        have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                        linarith
                · rcases le_total x (2151/2048:ℝ) with hc | hc
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                      · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                        have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                        have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                        have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
                        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
                        have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                        have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                        have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
                        have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                        have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                      · rcases le_total x (4297/4096:ℝ) with hc | hc
                        · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                          have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                          have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                          have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                          have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                          have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                          have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                          have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total x (4297/4096:ℝ) with hc | hc
                        · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                          have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                          have hw3 : (906687/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                          have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_873 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                          have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                          have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_889 (x + y + z) (by linarith) (by linarith)
                          linarith
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                      have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                      have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                      have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                      · rcases le_total x (4307/4096:ℝ) with hc | hc
                        · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                          have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                          have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                          have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_873 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                          have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                          have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                          have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_889 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                        have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                        linarith
          · rcases le_total x (1073/1024:ℝ) with hc | hc
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
                have hw5 : (160690591/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_824 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (1083/1024:ℝ) with hc | hc
                · rcases le_total x (2141/2048:ℝ) with hc | hc
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_333 (x + y) (by linarith) (by linarith)
                      have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_848 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                      have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_336 (x + y) (by linarith) (by linarith)
                      have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw3 : (3586667/1250000000000:ℝ) ≤ wfun (x + y) := wc_336 (x + y) (by linarith) (by linarith)
                      have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                      have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
                      have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_875 (x + y + z) (by linarith) (by linarith)
                      linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
                  have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
                  have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
                  have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
                have hw5 : (808657969/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_851 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (1083/1024:ℝ) with hc | hc
                · rcases le_total x (2151/2048:ℝ) with hc | hc
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
                      have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_875 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                      have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                      have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_900 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                      have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_900 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                      have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_927 (x + y + z) (by linarith) (by linarith)
                      linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
                  have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
                  have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
                  have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_929 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total y (1003/512:ℝ) with hc | hc
        · rcases le_total z (539/512:ℝ) with hc | hc
          · have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (3:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_321 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_327 (y + z) (by linarith) (by linarith))
            have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw1 : (9381492901/10000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
            have hw5 : (636617867/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_826 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (539/512:ℝ) with hc | hc
          · rcases le_total x (1083/1024:ℝ) with hc | hc
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · rcases le_total z (1073/1024:ℝ) with hc | hc
                · have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                  have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_823 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                  have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
                  have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_850 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (1073/1024:ℝ) with hc | hc
                · rcases le_total x (2161/2048:ℝ) with hc | hc
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                      have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                      have hw5 : (25514763/312500000000:ℝ) ≤ wfun (x + y + z) := wc_848 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (2141/2048:ℝ) with hc | hc
                      · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                        have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
                        have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
                        have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                      have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
                      have hw5 : (907100611/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                      have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
                      have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_337 (y + z) (by linarith) (by linarith)
                      have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_875 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total x (2161/2048:ℝ) with hc | hc
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                      have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                      have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                      have hw5 : (200453243/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_875 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (2151/2048:ℝ) with hc | hc
                      · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                        have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                        have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                        have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                        have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total y (4027/2048:ℝ) with hc | hc
                    · have hw1 : (118281741/156250000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                      have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                      have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_900 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw1 : (6990950273/10000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                      have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
                      have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_927 (x + y + z) (by linarith) (by linarith)
                      linarith
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
                have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_330 (y + z) (by linarith) (by linarith)
                have hw5 : (808657969/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_851 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (1073/1024:ℝ) with hc | hc
                · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
                  have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                  have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
                  have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_877 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
                  have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                  have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                  have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_929 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (1083/1024:ℝ) with hc | hc
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw5 : (198537007/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_878 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                have hw5 : (37329233/312500000000:ℝ) ≤ wfun (x + y + z) := wc_930 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (2011/1024:ℝ) with hc | hc
              · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
                have hw1 : (8154586159/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw5 : (37329233/312500000000:ℝ) ≤ wfun (x + y + z) := wc_930 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
                have hw1 : (697636487/1000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                have hw5 : (1413886087/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1018 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_37 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (1023/512:ℝ))
    (hz1 : (539/512:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1063/1024:ℝ) with hc | hc
  · rcases le_total y (2041/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2121/2048:ℝ) with hc | hc
        · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
          have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
          have hw3 : (235547/2000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
          have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
          have hw5 : (1424080951/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1016 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
          have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
          have hw3 : (5174037/5000000000000:ℝ) ≤ wfun (x + y) := wc_390 (x + y) (by linarith) (by linarith)
          have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
          have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1070 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
        have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
        have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
        have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
        have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1108 (x + y + z) (by linarith) (by linarith)
        linarith
    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
      have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
      have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
      have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1109 (x + y + z) (by linarith) (by linarith)
      linarith
  · rcases le_total y (2041/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2131/2048:ℝ) with hc | hc
        · rcases le_total y (4077/2048:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
            have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
            have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
            have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_553 (y + z) (by linarith) (by linarith)
            have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1106 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
            have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
            have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_561 (y + z) (by linarith) (by linarith)
            have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1134 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (4077/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4267/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_450 (x + y) (by linarith) (by linarith)
                have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
                have hw5 : (1798491653/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1132 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_466 (x + y) (by linarith) (by linarith)
                have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
                have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1142 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
              have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
              have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_560 (y + z) (by linarith) (by linarith)
              have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1148 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
            have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
            have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_561 (y + z) (by linarith) (by linarith)
            have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1149 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
        have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
        have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
        have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
        have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1151 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2131/2048:ℝ) with hc | hc
        · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
          have hw3 : (22987523/2500000000000:ℝ) ≤ wfun (x + y) := wc_482 (x + y) (by linarith) (by linarith)
          have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
          have hw5 : (1917416231/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1150 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
          have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_518 (x + y) (by linarith) (by linarith)
          have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
          have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1166 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
        have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
        have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
        have hw4 : (694482783/10000000000000:ℝ) ≤ wfun (y + z) := wc_570 (y + z) (by linarith) (by linarith)
        have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1172 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_41 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (529/512:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (2021/1024:ℝ) with hc | hc
  · rcases le_total z (1063/1024:ℝ) with hc | hc
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
        have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
        have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
        have hw5 : (498883881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_812 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
        have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
        have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
        have hw5 : (570814473/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_818 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4037/2048:ℝ) with hc | hc
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_333 (y + z) (by linarith) (by linarith)
            have hw5 : (162636919/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
            have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
            have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
            have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8079/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw4 : (18318183/10000000000000:ℝ) ≤ wfun (y + z) := wc_338 (y + z) (by linarith) (by linarith)
                have hw5 : (820415059/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
                have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8079/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                have hw4 : (18318183/10000000000000:ℝ) ≤ wfun (y + z) := wc_338 (y + z) (by linarith) (by linarith)
                have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
                have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (4037/2048:ℝ) with hc | hc
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_333 (y + z) (by linarith) (by linarith)
            have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_130 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
            have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
            have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
            have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
            have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
            have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8079/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                have hw4 : (18318183/10000000000000:ℝ) ≤ wfun (y + z) := wc_338 (y + z) (by linarith) (by linarith)
                have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_139 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
                have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
              have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_375 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (1063/1024:ℝ) with hc | hc
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4047/2048:ℝ) with hc | hc
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
          have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_361 (x + y) (by linarith) (by linarith)
          have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
          have hw5 : (648981217/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_821 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (2121/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
            have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
            have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
            have hw5 : (183045519/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
            have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
            have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (4047/2048:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
          have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
          have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_389 (x + y) (by linarith) (by linarith)
          have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
          have hw5 : (730420113/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (2121/2048:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
            have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
            have hw4 : (3586667/1250000000000:ℝ) ≤ wfun (y + z) := wc_336 (y + z) (by linarith) (by linarith)
            have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_151 y (by linarith) (by linarith)
            have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
            have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
            have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
            have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4047/2048:ℝ) with hc | hc
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (81942717/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_375 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (864332647/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_856 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8089/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                  have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
                  have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                  have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                  have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8089/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
                  have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
                  have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                  have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                  have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_866 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_872 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (8589/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
                    have hw5 : (264629371/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_886 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
                    have hw5 : (33866839/312500000000:ℝ) ≤ wfun (x + y + z) := wc_892 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (8589/8192:ℝ) with hc | hc
                  · rcases le_total y (16203/8192:ℝ) with hc | hc
                    · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                      have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                      have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                      have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                      have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (16203/8192:ℝ) with hc | hc
                    · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                      have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                      have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                      have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                      have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
                      linarith
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (8599/8192:ℝ) with hc | hc
                  · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
                    have hw5 : (554620627/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_895 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                    have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
                    have hw5 : (1135024061/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_904 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                  have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (8599/8192:ℝ) with hc | hc
                  · rcases le_total y (16203/8192:ℝ) with hc | hc
                    · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                      have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                      have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                      have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                      have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (16203/8192:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                      have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                      have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                      have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                      have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                      have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
                      linarith
      · rcases le_total y (4047/2048:ℝ) with hc | hc
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_388 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
              have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
              have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_404 (x + y) (by linarith) (by linarith)
              have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
              have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8089/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_872 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                  have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8089/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_31 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (2131/2048:ℝ) with hc | hc
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_872 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
                have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
                  have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (8609/8192:ℝ) with hc | hc
                  · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_434 (x + y) (by linarith) (by linarith)
                    have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                    have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                    have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_442 (x + y) (by linarith) (by linarith)
                    have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total y (8099/4096:ℝ) with hc | hc
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
                  have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_909 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                  have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
                  have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4267/4096:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                  have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                  have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_449 (x + y) (by linarith) (by linarith)
                  have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
                  linarith

set_option maxHeartbeats 20000000 in
lemma ch_59 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
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
  · rcases le_total x (4287/4096:ℝ) with hc | hc
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
          have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw5 : (192091031/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_864 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw5 : (984546007/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_868 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw5 : (192091031/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_864 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (153341/5000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
            have hw5 : (984546007/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_868 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw5 : (1009528097/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_869 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
          have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
          have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (153341/5000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
            have hw5 : (5167889/50000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
            have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
            have hw5 : (5167889/50000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (4287/4096:ℝ) with hc | hc
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (1085044203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_890 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
                have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (306931/10000000000000:ℝ) ≤ wfun (y + z) := wc_355 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_68 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (4047/2048:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (2151/2048:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4287/4096:ℝ) with hc | hc
  · rcases le_total y (8099/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
            have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
            have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
            have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
          have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
          have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
          have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
            have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
            have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
            have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
            have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
            have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
            have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total y (8099/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
            have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
            have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
            have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
            have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16193/8192:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
            have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
            have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
            have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
            have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
            have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16203/8192:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
            have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
            have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
            have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_100 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (8119/4096:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (4287/4096:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (8569/8192:ℝ) with hc | hc
  · rcases le_total y (16233/8192:ℝ) with hc | hc
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (1326087369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (1340083459/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_972 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17133/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (16233/8192:ℝ) with hc | hc
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (28822173/10000000000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (396991/125000000000:ℝ) ≤ wfun (y + z) := wc_423 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32461/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (8569/8192:ℝ) with hc | hc
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (1382484427/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_984 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
              have hw5 : (174594421/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_993 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17133/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (17143/16384:ℝ) with hc | hc
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (32471/16384:ℝ) with hc | hc
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
              have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (17143/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
              have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
              have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
              have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
              have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_107 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (4057/2048:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (2151/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4277/4096:ℝ) with hc | hc
  · rcases le_total y (8109/4096:ℝ) with hc | hc
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17103/16384:ℝ) with hc | hc
              · have hw0 : (1422414083/10000000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
            have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17103/16384:ℝ) with hc | hc
              · have hw0 : (1422414083/10000000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17103/16384:ℝ) with hc | hc
              · have hw0 : (1422414083/10000000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17103/16384:ℝ) with hc | hc
              · have hw0 : (1422414083/10000000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17103/16384:ℝ) with hc | hc
              · have hw0 : (1422414083/10000000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (8109/4096:ℝ) with hc | hc
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (32421/16384:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                  have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                  have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                  have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                  have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · rcases le_total y (32431/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                  have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                  have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                  have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                  have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32431/16384:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                  have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                  have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                  have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                  have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (32431/16384:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                  have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                  have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                  have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                  have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (32441/16384:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                  have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                  have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                  have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                  have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · rcases le_total y (32451/16384:ℝ) with hc | hc
                · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                  have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                  have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                  have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                  have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32451/16384:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                  have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                  have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                  have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                  have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · rcases le_total y (32441/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                  have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                  have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                  have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                  have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32441/16384:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                  have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                  have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                  have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                  have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · rcases le_total y (32441/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                  have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                  have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                  have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                  have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32441/16384:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                  have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                  have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                  have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                  have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · rcases le_total y (32451/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                  have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                  have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                  have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                  have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32451/16384:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                  have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                  have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                  have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                  have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · rcases le_total y (32451/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                  have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                  have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                  have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                  have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32451/16384:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                  have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                  have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                  have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                  have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_108 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (4057/2048:ℝ))
    (hz1 : (2151/2048:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4277/4096:ℝ) with hc | hc
  · rcases le_total y (8109/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
            have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
            have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
            have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
            have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
          have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
          have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
          have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
          have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
          have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
          have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1001 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
            have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
            have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
            have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
            have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
          have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
          have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
          have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1010 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
          have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
          have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
          have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total y (8109/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
            have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
            have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
            have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
            have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
            have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
            have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
            have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
            have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
            have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
            have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
            have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
            have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_110 (x y z : ℝ) (hx1 : (4277/4096:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (2151/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8119/4096:ℝ) with hc | hc
  · rcases le_total z (4297/4096:ℝ) with hc | hc
    · rcases le_total x (8559/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8559/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
            have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
            have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
            have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
            have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (4297/4096:ℝ) with hc | hc
    · rcases le_total x (8559/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8559/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
            have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
            have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_112 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (8109/4096:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (2151/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (4297/4096:ℝ) with hc | hc
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8589/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8589/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8589/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8589/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8599/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
            have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
            have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
            have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
            have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
            have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
            have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
            have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
            have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
            have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
            have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (8599/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
            have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
            have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
            have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
            have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
            have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
            have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
            have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (16213/8192:ℝ) with hc | hc
      · rcases le_total z (8599/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
            have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
            have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
            have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (32421/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
            have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
            have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
            have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
            have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (8599/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32431/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
            have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
            have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
            have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
            have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_150 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (4297/4096:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (4057/2048:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (2151/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8109/4096:ℝ) with hc | hc
  · rcases le_total z (4297/4096:ℝ) with hc | hc
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
            have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
            have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (4297/4096:ℝ) with hc | hc
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
            have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
            have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_201 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (3019/1024:ℝ) ≤ y) (hy2 : y ≤ (1525/512:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (267/256:ℝ) with hc | hc
  · rcases le_total y (6069/2048:ℝ) with hc | hc
    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
      have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_298 y (by linarith) (by linarith)
      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
      have hw3 : (34242453/10000000000000:ℝ) ≤ wfun (x + y) := by
        rcases le_total (x + y) (4:ℝ) with hq30 | hq30
        · exact le_trans (by norm_num) (wc_638 (x + y) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_669 (x + y) (by linarith) (by linarith))
      have hw4 : (34242453/10000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_638 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_669 (y + z) (by linarith) (by linarith))
      linarith
    · rcases le_total x (529/512:ℝ) with hc | hc
      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
        have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
        have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
        have hw3 : (2673983/5000000000000:ℝ) ≤ wfun (x + y) := by
          rcases le_total (x + y) (4:ℝ) with hq30 | hq30
          · exact le_trans (by norm_num) (wc_651 (x + y) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_675 (x + y) (by linarith) (by linarith))
        linarith
      · rcases le_total z (529/512:ℝ) with hc | hc
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
          have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
          have hw4 : (2673983/5000000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (4:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_651 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_675 (y + z) (by linarith) (by linarith))
          have hw5 : (8145961/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1225 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
          have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
          have hw5 : (82109019/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1243 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total y (6069/2048:ℝ) with hc | hc
    · rcases le_total x (529/512:ℝ) with hc | hc
      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
        have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_298 y (by linarith) (by linarith)
        have hw3 : (30026951/2000000000000:ℝ) ≤ wfun (x + y) := wc_637 (x + y) (by linarith) (by linarith)
        have hw5 : (790561/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1214 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total z (539/512:ℝ) with hc | hc
        · rcases le_total y (12107/4096:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
            have hw3 : (23464061/2000000000000:ℝ) ≤ wfun (x + y) := wc_646 (x + y) (by linarith) (by linarith)
            have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_653 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_671 (y + z) (by linarith) (by linarith))
            have hw5 : (7987727/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1230 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
              have hw3 : (16474823/2000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_652 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_662 (x + y) (by linarith) (by linarith))
              have hw5 : (104831431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1245 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
              have hw3 : (34242453/10000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_655 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_669 (x + y) (by linarith) (by linarith))
              have hw5 : (81281811/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1258 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (12107/4096:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
            have hw3 : (23464061/2000000000000:ℝ) ≤ wfun (x + y) := wc_646 (x + y) (by linarith) (by linarith)
            have hw5 : (64386099/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1251 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
            have hw3 : (34242453/10000000000000:ℝ) ≤ wfun (x + y) := by
              rcases le_total (x + y) (4:ℝ) with hq30 | hq30
              · exact le_trans (by norm_num) (wc_652 (x + y) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_669 (x + y) (by linarith) (by linarith))
            have hw5 : (115886053/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1280 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (529/512:ℝ) with hc | hc
      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
        have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
        have hw3 : (2673983/5000000000000:ℝ) ≤ wfun (x + y) := by
          rcases le_total (x + y) (4:ℝ) with hq30 | hq30
          · exact le_trans (by norm_num) (wc_651 (x + y) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_675 (x + y) (by linarith) (by linarith))
        have hw5 : (81477507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1244 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total z (539/512:ℝ) with hc | hc
        · rcases le_total y (12169/4096:ℝ) with hc | hc
          · rcases le_total x (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
              have hw3 : (8327617/5000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_657 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_672 (x + y) (by linarith) (by linarith))
              have hw5 : (99799521/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1274 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (1073/1024:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (752127/10000000000000:ℝ) ≤ wfun (x + y) := wc_682 (x + y) (by linarith) (by linarith)
                have hw5 : (4336279/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1293 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (752127/10000000000000:ℝ) ≤ wfun (x + y) := wc_682 (x + y) (by linarith) (by linarith)
                have hw5 : (183435743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1318 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
              have hw5 : (10122207/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1305 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (1073/1024:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw5 : (421158101/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1330 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw4 : (1350713/2500000000000:ℝ) ≤ wfun (y + z) := wc_726 (y + z) (by linarith) (by linarith)
                have hw5 : (529106123/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1360 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (12169/4096:ℝ) with hc | hc
          · rcases le_total x (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
              have hw3 : (8327617/5000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_657 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_672 (x + y) (by linarith) (by linarith))
              have hw4 : (163329/5000000000000:ℝ) ≤ wfun (y + z) := wc_713 (y + z) (by linarith) (by linarith)
              have hw5 : (73091573/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1319 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
              have hw3 : (752127/10000000000000:ℝ) ≤ wfun (x + y) := wc_682 (x + y) (by linarith) (by linarith)
              have hw4 : (163329/5000000000000:ℝ) ≤ wfun (y + z) := wc_713 (y + z) (by linarith) (by linarith)
              have hw5 : (58307863/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1348 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
            have hw4 : (7532357/2500000000000:ℝ) ≤ wfun (y + z) := wc_752 (y + z) (by linarith) (by linarith)
            have hw5 : (13126113/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1361 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_212 (x y z : ℝ) (hx1 : (63/32:ℝ) ≤ x) (hx2 : x ≤ (131/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (17/16:ℝ))
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

end Zeta23Ext.Bridge.FourPoint
