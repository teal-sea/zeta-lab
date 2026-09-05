import FourPoint.Cells

/-! Chunk module 4 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_6 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (247/128:ℝ) ≤ y) (hy2 : y ≤ (63/32:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (131/128:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  have hw1 : (6731724963/10000000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
  have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
    rcases le_total z (1:ℝ) with hq20 | hq20
    · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
    exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
  have hw4 : (288828359/5000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
  linarith

set_option maxHeartbeats 20000000 in
lemma ch_16 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (529/512:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (1013/512:ℝ) with hc | hc
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total x (1053/1024:ℝ) with hc | hc
      · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
        have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
        have hw3 : (70009749/5000000000000:ℝ) ≤ wfun (x + y) := by
          rcases le_total (x + y) (3:ℝ) with hq30 | hq30
          · exact le_trans (by norm_num) (wc_321 (x + y) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_325 (x + y) (by linarith) (by linarith))
        have hw5 : (165310021/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_782 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (2021/1024:ℝ) with hc | hc
        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
          have hw3 : (70009749/5000000000000:ℝ) ≤ wfun (x + y) := by
            rcases le_total (x + y) (3:ℝ) with hq30 | hq30
            · exact le_trans (by norm_num) (wc_323 (x + y) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_325 (x + y) (by linarith) (by linarith))
          have hw5 : (128356097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_795 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
          have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_144 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
          have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
          have hw5 : (183260287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_803 (x + y + z) (by linarith) (by linarith)
          linarith
    · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
      have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
        rcases le_total (x + y) (3:ℝ) with hq30 | hq30
        · exact le_trans (by norm_num) (wc_321 (x + y) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_327 (x + y) (by linarith) (by linarith))
      have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
      have hw5 : (90752099/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
      linarith
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total x (1053/1024:ℝ) with hc | hc
      · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
        have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
        have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
        have hw4 : (231767/2000000000000:ℝ) ≤ wfun (y + z) := wc_365 (y + z) (by linarith) (by linarith)
        have hw5 : (182379599/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_804 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
            have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
            have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_363 (y + z) (by linarith) (by linarith)
            have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_813 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
            have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
            have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
            have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_823 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2111/2048:ℝ) with hc | hc
            · have hw0 : (2866556697/5000000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
              have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
              have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
              have hw5 : (323709737/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_822 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
              have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
              have hw5 : (728663451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_841 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
            have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_850 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (1053/1024:ℝ) with hc | hc
      · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
        have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
        have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
        have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
        have hw5 : (79960111/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_825 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
          have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
          have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
          have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_484 (y + z) (by linarith) (by linarith)
          have hw5 : (808657969/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_851 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_15 x (by linarith) (by linarith)
          have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_534 (y + z) (by linarith) (by linarith)
          have hw5 : (198537007/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_878 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_49 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (4067/2048:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (1063/1024:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (2131/2048:ℝ) with hc | hc
  · rcases le_total x (4287/4096:ℝ) with hc | hc
    · rcases le_total y (8139/4096:ℝ) with hc | hc
      · rcases le_total z (4257/4096:ℝ) with hc | hc
        · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
          have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
          have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
          have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_479 (x + y) (by linarith) (by linarith)
          have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
          have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_499 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_955 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4257/4096:ℝ) with hc | hc
        · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
          have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
          have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
          have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
          have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
          have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
          have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
          have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
          have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
          have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
          have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (8139/4096:ℝ) with hc | hc
      · rcases le_total z (4257/4096:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
          have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
          have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
          have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_506 (x + y) (by linarith) (by linarith)
          have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
          have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_505 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_511 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_980 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4257/4096:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
          have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
          have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
          have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
          have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
          have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
          have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
          have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
          have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
          have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
          have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_990 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total x (4287/4096:ℝ) with hc | hc
    · rcases le_total y (8139/4096:ℝ) with hc | hc
      · rcases le_total z (4267/4096:ℝ) with hc | hc
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8539/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8539/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8539/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8539/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4267/4096:ℝ) with hc | hc
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
              have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
              have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
              have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
              have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · rcases le_total z (8539/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
              have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · rcases le_total z (8539/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
              have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (8139/4096:ℝ) with hc | hc
      · rcases le_total z (4267/4096:ℝ) with hc | hc
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8539/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8539/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8539/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8539/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4267/4096:ℝ) with hc | hc
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
              have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
              have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
            have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
            have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
            have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
              have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
              have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
              have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
              have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
              have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_61 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (4047/2048:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8099/4096:ℝ) with hc | hc
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
            have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (2641873/10000000000000:ℝ) ≤ wfun (x + y) := wc_367 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (716733/2000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (2641873/10000000000000:ℝ) ≤ wfun (x + y) := wc_367 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (716733/2000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
            have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (2641873/10000000000000:ℝ) ≤ wfun (x + y) := wc_367 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (716733/2000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1162834311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_905 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1175989937/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_912 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (245935877/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_932 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (245935877/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_932 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (7269931/10000000000000:ℝ) ≤ wfun (x + y) := wc_377 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (7269931/10000000000000:ℝ) ≤ wfun (x + y) := wc_377 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (7269931/10000000000000:ℝ) ≤ wfun (x + y) := wc_377 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (7269931/10000000000000:ℝ) ≤ wfun (x + y) := wc_377 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_62 (x y z : ℝ) (hx1 : (4287/4096:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (4047/2048:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8099/4096:ℝ) with hc | hc
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
            have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
            have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (7266981/10000000000000:ℝ) ≤ wfun (y + z) := wc_378 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (4390211/5000000000000:ℝ) ≤ wfun (y + z) := wc_382 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (5218271/5000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (2447049/2000000000000:ℝ) ≤ wfun (y + z) := wc_392 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_65 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (2021/1024:ℝ) ≤ y) (hy2 : y ≤ (4047/2048:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (2151/2048:ℝ) with hc | hc
  · rcases le_total x (4287/4096:ℝ) with hc | hc
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total x (4287/4096:ℝ) with hc | hc
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
          have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8569/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (153341/5000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_980 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (153341/5000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_980 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8579/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1001 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_99 (x y z : ℝ) (hx1 : (4287/4096:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
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
  · rcases le_total x (8579/8192:ℝ) with hc | hc
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8549/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (8579/8192:ℝ) with hc | hc
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (1411094809/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_996 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17153/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16243/8192:ℝ) with hc | hc
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · rcases le_total z (17123/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (585927977/5000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (8709539/2500000000000:ℝ) ≤ wfun (y + z) := wc_425 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32481/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8559/8192:ℝ) with hc | hc
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17163/16384:ℝ) with hc | hc
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32491/16384:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_130 (x y z : ℝ) (hx1 : (4287/4096:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (4067/2048:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8129/4096:ℝ) with hc | hc
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16253/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · rcases le_total z (17133/16384:ℝ) with hc | hc
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (1055892761/10000000000000:ℝ) ≤ wfun z := wc_53 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                  have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                  have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · rcases le_total z (17143/16384:ℝ) with hc | hc
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                  have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                  have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · rcases le_total z (17143/16384:ℝ) with hc | hc
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (236527239/2500000000000:ℝ) ≤ wfun z := wc_58 z (by linarith) (by linarith)
                  have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                  have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                  have hw5 : (15432181/100000000000:ℝ) ≤ wfun (x + y + z) := wc_1056 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                  have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                  have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                  have hw5 : (7791189/50000000000:ℝ) ≤ wfun (x + y + z) := wc_1059 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16253/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16253/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16253/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32501/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32511/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (332952481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1096 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16263/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32521/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32521/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32521/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32521/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32531/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3651040643/10000000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3600349479/10000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (108771831/10000000000000:ℝ) ≤ wfun (x + y) := wc_500 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16263/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32521/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (108771831/10000000000000:ℝ) ≤ wfun (x + y) := wc_500 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32521/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (108771831/10000000000000:ℝ) ≤ wfun (x + y) := wc_500 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (114385137/10000000000000:ℝ) ≤ wfun (x + y) := wc_502 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32521/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (108771831/10000000000000:ℝ) ≤ wfun (x + y) := wc_500 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32521/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (108771831/10000000000000:ℝ) ≤ wfun (x + y) := wc_500 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (114385137/10000000000000:ℝ) ≤ wfun (x + y) := wc_502 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16263/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32521/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32521/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16263/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (342221649/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1112 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (1726856719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1116 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_144 (x y z : ℝ) (hx1 : (4297/4096:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (2141/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8119/4096:ℝ) with hc | hc
  · rcases le_total z (4277/4096:ℝ) with hc | hc
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
            have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
            have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
            have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
            have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
            have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17203/16384:ℝ) with hc | hc
            · have hw0 : (207931583/5000000000000:ℝ) ≤ wfun x := wc_81 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_83 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (4277/4096:ℝ) with hc | hc
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
            have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
            have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (8599/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17193/16384:ℝ) with hc | hc
            · have hw0 : (244530967/5000000000000:ℝ) ≤ wfun x := wc_77 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_80 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
            have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
            have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
            have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
            have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
            have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_149 (x y z : ℝ) (hx1 : (2151/2048:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
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
    · rcases le_total y (8119/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (8119/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_511 (x + y) (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total x (4307/4096:ℝ) with hc | hc
    · rcases le_total y (8119/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
              have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8609/8192:ℝ) with hc | hc
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (31733701/1000000000000:ℝ) ≤ wfun x := wc_84 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
              have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_87 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
              have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (8119/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
              have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
              have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16233/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
              have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
              have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
              have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
              have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
            have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
            have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8619/8192:ℝ) with hc | hc
          · rcases le_total y (16243/8192:ℝ) with hc | hc
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
              have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (25860883/1250000000000:ℝ) ≤ wfun x := wc_88 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
              have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_90 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
            have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
            have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_176 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (1023/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (2041/1024:ℝ) with hc | hc
  · rcases le_total z (1073/1024:ℝ) with hc | hc
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4077/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · rcases le_total x (8589/8192:ℝ) with hc | hc
                  · rcases le_total y (16293/8192:ℝ) with hc | hc
                    · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                      have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                      have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                      have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                      have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                      have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                      have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                      have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                      have hw3 : (25929173/1250000000000:ℝ) ≤ wfun (x + y) := wc_535 (x + y) (by linarith) (by linarith)
                      have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                      have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
                    have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                    have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (8589/8192:ℝ) with hc | hc
                  · rcases le_total y (16293/8192:ℝ) with hc | hc
                    · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                      have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                      have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                      have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                      have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                      have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                      have hw3 : (25929173/1250000000000:ℝ) ≤ wfun (x + y) := wc_535 (x + y) (by linarith) (by linarith)
                      have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                      have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total y (16293/8192:ℝ) with hc | hc
                    · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                      have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                      have hw3 : (25929173/1250000000000:ℝ) ≤ wfun (x + y) := wc_535 (x + y) (by linarith) (by linarith)
                      have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                      have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                      have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                      have hw3 : (111478321/5000000000000:ℝ) ≤ wfun (x + y) := wc_537 (x + y) (by linarith) (by linarith)
                      have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                      have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · rcases le_total x (8589/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (44555321/2000000000000:ℝ) ≤ wfun (x + y) := wc_538 (x + y) (by linarith) (by linarith)
                    have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                    have hw5 : (43501511/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1120 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (238838563/10000000000000:ℝ) ≤ wfun (x + y) := wc_541 (x + y) (by linarith) (by linarith)
                    have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                    have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (8589/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (44555321/2000000000000:ℝ) ≤ wfun (x + y) := wc_538 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (180388897/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1129 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (238838563/10000000000000:ℝ) ≤ wfun (x + y) := wc_541 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · rcases le_total x (8599/8192:ℝ) with hc | hc
                  · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (44555321/2000000000000:ℝ) ≤ wfun (x + y) := wc_538 (x + y) (by linarith) (by linarith)
                    have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                    have hw5 : (43501511/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1120 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                    have hw3 : (238838563/10000000000000:ℝ) ≤ wfun (x + y) := wc_541 (x + y) (by linarith) (by linarith)
                    have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                    have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (8599/8192:ℝ) with hc | hc
                  · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (44555321/2000000000000:ℝ) ≤ wfun (x + y) := wc_538 (x + y) (by linarith) (by linarith)
                    have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                    have hw5 : (180388897/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1129 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                    have hw3 : (238838563/10000000000000:ℝ) ≤ wfun (x + y) := wc_541 (x + y) (by linarith) (by linarith)
                    have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                    have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                  have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                  have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · rcases le_total x (8589/8192:ℝ) with hc | hc
                  · rcases le_total y (16293/8192:ℝ) with hc | hc
                    · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                      have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                      have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                      have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
                      have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                      have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                      have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                      have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                      have hw3 : (25929173/1250000000000:ℝ) ≤ wfun (x + y) := wc_535 (x + y) (by linarith) (by linarith)
                      have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                      have hw5 : (183730059/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1136 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (8589/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (19230721/1000000000000:ℝ) ≤ wfun (x + y) := wc_528 (x + y) (by linarith) (by linarith)
                    have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                    have hw5 : (1868773189/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1139 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                    have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
                    have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                    have hw5 : (950804677/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1144 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · rcases le_total x (8589/8192:ℝ) with hc | hc
                  · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                    have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (44555321/2000000000000:ℝ) ≤ wfun (x + y) := wc_538 (x + y) (by linarith) (by linarith)
                    have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                    have hw5 : (1868773189/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1139 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                    have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (238838563/10000000000000:ℝ) ≤ wfun (x + y) := wc_541 (x + y) (by linarith) (by linarith)
                    have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                    have hw5 : (950804677/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1144 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                  have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · rcases le_total x (8599/8192:ℝ) with hc | hc
                  · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (44555321/2000000000000:ℝ) ≤ wfun (x + y) := wc_538 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (1868773189/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1139 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                    have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                    have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                    have hw3 : (238838563/10000000000000:ℝ) ≤ wfun (x + y) := wc_541 (x + y) (by linarith) (by linarith)
                    have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                    have hw5 : (950804677/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1144 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                  have hw5 : (2000486673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1158 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                  have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                  have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                  have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                  have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                  have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (65423973/2000000000000:ℝ) ≤ wfun (x + y) := wc_550 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
                have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                  have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                  have hw5 : (2000486673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1158 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
                have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1159 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
                have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1159 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (65423973/2000000000000:ℝ) ≤ wfun (x + y) := wc_550 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
                have hw5 : (129124203/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1162 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (4077/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
                  have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                  have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                  have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
                  have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                  have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                  have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_480 (y + z) (by linarith) (by linarith)
                have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1141 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (65423973/2000000000000:ℝ) ≤ wfun (x + y) := wc_550 (x + y) (by linarith) (by linarith)
                have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_507 (y + z) (by linarith) (by linarith)
                have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
                  have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                  have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
                  have hw5 : (2000486673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1158 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
                have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1159 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
                have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1159 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (65423973/2000000000000:ℝ) ≤ wfun (x + y) := wc_550 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
                have hw5 : (129124203/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1162 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (65423973/2000000000000:ℝ) ≤ wfun (x + y) := wc_550 (x + y) (by linarith) (by linarith)
                have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_516 (y + z) (by linarith) (by linarith)
                have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (9158301/250000000000:ℝ) ≤ wfun (x + y) := wc_558 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_524 (y + z) (by linarith) (by linarith)
                have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1159 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (365741913/10000000000000:ℝ) ≤ wfun (x + y) := wc_559 (x + y) (by linarith) (by linarith)
              have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
              have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1160 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (65423973/2000000000000:ℝ) ≤ wfun (x + y) := wc_550 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
                have hw5 : (129124203/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1162 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (9158301/250000000000:ℝ) ≤ wfun (x + y) := wc_558 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
                have hw5 : (16679003/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1167 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (365741913/10000000000000:ℝ) ≤ wfun (x + y) := wc_559 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
              have hw5 : (426471879/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1168 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4077/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4297/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                  have hw5 : (386709691/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1145 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
                  have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                  have hw5 : (2000486673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1158 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4297/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                  have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                  have hw5 : (2000486673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1158 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                  have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
                  have hw5 : (1034231129/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1161 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4297/4096:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
                  have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
                  have hw5 : (2000486673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1158 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
                  have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                  have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
                  have hw5 : (1034231129/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1161 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
                have hw5 : (129124203/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1162 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
                have hw4 : (10193319/400000000000:ℝ) ≤ wfun (y + z) := wc_543 (y + z) (by linarith) (by linarith)
                have hw5 : (129124203/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1162 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_539 (x + y) (by linarith) (by linarith)
                have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
                have hw5 : (16679003/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1167 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
              have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_540 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
              have hw5 : (426471879/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1168 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                have hw4 : (10193319/400000000000:ℝ) ≤ wfun (y + z) := wc_543 (y + z) (by linarith) (by linarith)
                have hw5 : (129124203/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1162 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                have hw4 : (289620509/10000000000000:ℝ) ≤ wfun (y + z) := wc_549 (y + z) (by linarith) (by linarith)
                have hw5 : (16679003/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1167 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_549 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
              have hw5 : (426471879/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1168 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (4077/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_216 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_542 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
                have hw5 : (129124203/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1162 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_85 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_548 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
                have hw5 : (16679003/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1167 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_89 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
              have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_549 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
              have hw5 : (426471879/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1168 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
            have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
            have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (1171101043/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1175 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (1073/1024:ℝ) with hc | hc
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4087/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8169/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (2327527631/10000000000000:ℝ) ≤ wfun y := wc_228 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (65423973/2000000000000:ℝ) ≤ wfun (x + y) := wc_550 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_530 (y + z) (by linarith) (by linarith)
                have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1146 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
                have hw1 : (2168970253/10000000000000:ℝ) ≤ wfun y := wc_231 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (9158301/250000000000:ℝ) ≤ wfun (x + y) := wc_558 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_540 (y + z) (by linarith) (by linarith)
                have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1159 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
              have hw3 : (365741913/10000000000000:ℝ) ≤ wfun (x + y) := wc_559 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
              have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1160 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (326592691/10000000000000:ℝ) ≤ wfun (x + y) := wc_551 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
              have hw5 : (103175797/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1163 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
              have hw3 : (365741913/10000000000000:ℝ) ≤ wfun (x + y) := wc_559 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
              have hw5 : (426471879/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1168 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
            have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
            have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (4087/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
            have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
            have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
            have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
          have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
          have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_562 (x + y) (by linarith) (by linarith)
          have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_545 (y + z) (by linarith) (by linarith)
          have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1170 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4087/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
            have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
            have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
            have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
            have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_560 (y + z) (by linarith) (by linarith)
            have hw5 : (1171101043/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1175 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
          have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
          have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_561 (y + z) (by linarith) (by linarith)
          have hw5 : (2336612903/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1176 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (4087/2048:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
          have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
          have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_553 (y + z) (by linarith) (by linarith)
          have hw5 : (2336612903/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1176 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
          have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_562 (x + y) (by linarith) (by linarith)
          have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_561 (y + z) (by linarith) (by linarith)
          have hw5 : (1241444043/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1178 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_202 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (3019/1024:ℝ) ≤ y) (hy2 : y ≤ (1525/512:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (6069/2048:ℝ) with hc | hc
  · rcases le_total x (539/512:ℝ) with hc | hc
    · rcases le_total z (529/512:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
        have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_298 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw4 : (30026951/2000000000000:ℝ) ≤ wfun (y + z) := wc_637 (y + z) (by linarith) (by linarith)
        have hw5 : (796707/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1213 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (12107/4096:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
          have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
          have hw3 : (9692591/5000000000000:ℝ) ≤ wfun (x + y) := by
            rcases le_total (x + y) (4:ℝ) with hq30 | hq30
            · exact le_trans (by norm_num) (wc_653 (x + y) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_671 (x + y) (by linarith) (by linarith))
          have hw4 : (23464061/2000000000000:ℝ) ≤ wfun (y + z) := wc_646 (y + z) (by linarith) (by linarith)
          have hw5 : (7987727/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1230 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (1073/1024:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
            have hw3 : (6937709/10000000000000:ℝ) ≤ wfun (x + y) := by
              rcases le_total (x + y) (4:ℝ) with hq30 | hq30
              · exact le_trans (by norm_num) (wc_659 (x + y) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_674 (x + y) (by linarith) (by linarith))
            have hw4 : (34242453/10000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_652 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_669 (y + z) (by linarith) (by linarith))
            have hw5 : (104831431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1245 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
            have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
            have hw4 : (34242453/10000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_652 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_669 (y + z) (by linarith) (by linarith))
            have hw5 : (81281811/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1258 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (529/512:ℝ) with hc | hc
      · have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_298 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw4 : (30026951/2000000000000:ℝ) ≤ wfun (y + z) := wc_637 (y + z) (by linarith) (by linarith)
        have hw5 : (39699707/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1231 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (12107/4096:ℝ) with hc | hc
        · have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
          have hw4 : (23464061/2000000000000:ℝ) ≤ wfun (y + z) := wc_646 (y + z) (by linarith) (by linarith)
          have hw5 : (64386099/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1251 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
          have hw4 : (34242453/10000000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (4:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_652 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_669 (y + z) (by linarith) (by linarith))
          have hw5 : (115886053/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1280 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total x (539/512:ℝ) with hc | hc
    · rcases le_total z (529/512:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
        have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw4 : (2673983/5000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_651 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_675 (y + z) (by linarith) (by linarith))
        have hw5 : (82109019/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1243 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (12169/4096:ℝ) with hc | hc
        · rcases le_total x (1073/1024:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
            have hw4 : (752127/10000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_657 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_676 (y + z) (by linarith) (by linarith))
            have hw5 : (99799521/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1274 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw4 : (8327617/5000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_657 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_672 (y + z) (by linarith) (by linarith))
              have hw5 : (4336279/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1293 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw4 : (752127/10000000000000:ℝ) ≤ wfun (y + z) := wc_682 (y + z) (by linarith) (by linarith)
              have hw5 : (183435743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1318 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (1073/1024:ℝ) with hc | hc
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw5 : (325164083/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1304 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw5 : (421158101/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1330 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw3 : (1350713/2500000000000:ℝ) ≤ wfun (x + y) := wc_726 (x + y) (by linarith) (by linarith)
              have hw5 : (421158101/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1330 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (1350713/2500000000000:ℝ) ≤ wfun (x + y) := wc_726 (x + y) (by linarith) (by linarith)
              have hw5 : (529106123/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1360 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (529/512:ℝ) with hc | hc
      · have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
        have hw3 : (32421/1000000000000:ℝ) ≤ wfun (x + y) := wc_714 (x + y) (by linarith) (by linarith)
        have hw4 : (2673983/5000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_651 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_675 (y + z) (by linarith) (by linarith))
        have hw5 : (19764329/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1275 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (12169/4096:ℝ) with hc | hc
        · rcases le_total x (1083/1024:ℝ) with hc | hc
          · rcases le_total z (1063/1024:ℝ) with hc | hc
            · have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
              have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_18 z (by linarith) (by linarith)
              have hw3 : (1313/40000000000:ℝ) ≤ wfun (x + y) := wc_712 (x + y) (by linarith) (by linarith)
              have hw4 : (8327617/5000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_657 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_672 (y + z) (by linarith) (by linarith))
              have hw5 : (183435743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1318 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_25 z (by linarith) (by linarith)
              have hw3 : (1313/40000000000:ℝ) ≤ wfun (x + y) := wc_712 (x + y) (by linarith) (by linarith)
              have hw4 : (752127/10000000000000:ℝ) ≤ wfun (y + z) := wc_682 (y + z) (by linarith) (by linarith)
              have hw5 : (234132737/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1347 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
            have hw3 : (3526053/2500000000000:ℝ) ≤ wfun (x + y) := wc_736 (x + y) (by linarith) (by linarith)
            have hw4 : (752127/10000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_657 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_676 (y + z) (by linarith) (by linarith))
            have hw5 : (58307863/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1348 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
          have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
          have hw3 : (7532357/2500000000000:ℝ) ≤ wfun (x + y) := wc_752 (x + y) (by linarith) (by linarith)
          have hw5 : (13126113/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1361 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_207 (x y z : ℝ) (hx1 : (17/16:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (747/256:ℝ) ≤ y) (hy2 : y ≤ (389/128:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (17/16:ℝ) with hc | hc
  · rcases le_total y (1525/512:ℝ) with hc | hc
    · rcases le_total x (141/128:ℝ) with hc | hc
      · rcases le_total z (131/128:ℝ) with hc | hc
        · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
          have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_292 y (by linarith) (by linarith)
          have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
            rcases le_total z (1:ℝ) with hq20 | hq20
            · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
          have hw4 : (76620491/10000000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (4:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_626 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_663 (y + z) (by linarith) (by linarith))
          linarith
        · rcases le_total y (3019/1024:ℝ) with hc | hc
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total z (267/256:ℝ) with hc | hc
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_291 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                have hw4 : (122092393/5000000000000:ℝ) ≤ wfun (y + z) := wc_629 (y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (6007/2048:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                  have hw1 : (2995265257/5000000000000:ℝ) ≤ wfun y := wc_290 y (by linarith) (by linarith)
                  have hw3 : (4221/10000000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_644 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_677 (x + y) (by linarith) (by linarith))
                  have hw4 : (82600037/5000000000000:ℝ) ≤ wfun (y + z) := wc_633 (y + z) (by linarith) (by linarith)
                  have hw5 : (33101423/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1226 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                  have hw1 : (816631931/2000000000000:ℝ) ≤ wfun y := wc_294 y (by linarith) (by linarith)
                  have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_640 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_673 (y + z) (by linarith) (by linarith))
                  have hw5 : (181069953/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1260 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_107 x (by linarith) (by linarith)
              have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_291 y (by linarith) (by linarith)
              have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_630 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_673 (y + z) (by linarith) (by linarith))
              have hw5 : (32210921/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1227 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total z (267/256:ℝ) with hc | hc
              · rcases le_total y (6069/2048:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                  have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_298 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                  have hw4 : (34242453/10000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_638 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_669 (y + z) (by linarith) (by linarith))
                  have hw5 : (31511369/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1252 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total z (529/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                      have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
                      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                      have hw3 : (9485773/2000000000000:ℝ) ≤ wfun (x + y) := wc_762 (x + y) (by linarith) (by linarith)
                      have hw4 : (2673983/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_651 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_675 (y + z) (by linarith) (by linarith))
                      have hw5 : (1130887/31250000000:ℝ) ≤ wfun (x + y + z) := wc_1320 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                      have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_19 z (by linarith) (by linarith)
                      have hw3 : (9485773/2000000000000:ℝ) ≤ wfun (x + y) := wc_762 (x + y) (by linarith) (by linarith)
                      have hw5 : (57364627/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1377 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_106 x (by linarith) (by linarith)
                    have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                    have hw3 : (86688141/5000000000000:ℝ) ≤ wfun (x + y) := wc_789 (x + y) (by linarith) (by linarith)
                    have hw5 : (569259631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1378 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (6069/2048:ℝ) with hc | hc
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total z (539/512:ℝ) with hc | hc
                    · rcases le_total y (12107/4096:ℝ) with hc | hc
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                        have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                        have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_653 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_671 (y + z) (by linarith) (by linarith))
                        have hw5 : (227036969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1342 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                        have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                        have hw3 : (2002543/5000000000000:ℝ) ≤ wfun (x + y) := wc_722 (x + y) (by linarith) (by linarith)
                        have hw5 : (63145721/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1390 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                      have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_298 y (by linarith) (by linarith)
                      have hw5 : (342044549/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1402 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_106 x (by linarith) (by linarith)
                    have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_298 y (by linarith) (by linarith)
                    have hw3 : (11672323/10000000000000:ℝ) ≤ wfun (x + y) := wc_735 (x + y) (by linarith) (by linarith)
                    have hw5 : (339431207/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1403 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total z (539/512:ℝ) with hc | hc
                    · rcases le_total y (12169/4096:ℝ) with hc | hc
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                        have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_307 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                        have hw3 : (9557219/2000000000000:ℝ) ≤ wfun (x + y) := wc_761 (x + y) (by linarith) (by linarith)
                        have hw5 : (418269633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1439 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                        have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_311 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
                        have hw3 : (17410303/1250000000000:ℝ) ≤ wfun (x + y) := wc_779 (x + y) (by linarith) (by linarith)
                        have hw5 : (534301079/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1467 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_101 x (by linarith) (by linarith)
                      have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
                      have hw3 : (9485773/2000000000000:ℝ) ≤ wfun (x + y) := wc_762 (x + y) (by linarith) (by linarith)
                      have hw4 : (32421/1000000000000:ℝ) ≤ wfun (y + z) := wc_714 (y + z) (by linarith) (by linarith)
                      have hw5 : (1134166649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1477 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_106 x (by linarith) (by linarith)
                    have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_308 y (by linarith) (by linarith)
                    have hw3 : (86688141/5000000000000:ℝ) ≤ wfun (x + y) := wc_789 (x + y) (by linarith) (by linarith)
                    have hw5 : (1125526841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1478 (x + y + z) (by linarith) (by linarith)
                    linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_107 x (by linarith) (by linarith)
              have hw1 : (67339097/500000000000:ℝ) ≤ wfun y := wc_299 y (by linarith) (by linarith)
              have hw3 : (92147329/10000000000000:ℝ) ≤ wfun (x + y) := wc_773 (x + y) (by linarith) (by linarith)
              have hw5 : (432607663/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1344 (x + y + z) (by linarith) (by linarith)
              linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_108 x (by linarith) (by linarith)
        have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_292 y (by linarith) (by linarith)
        have hw3 : (1440757/2000000000000:ℝ) ≤ wfun (x + y) := wc_729 (x + y) (by linarith) (by linarith)
        linarith
    · rcases le_total x (141/128:ℝ) with hc | hc
      · rcases le_total z (131/128:ℝ) with hc | hc
        · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
          have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
            rcases le_total z (1:ℝ) with hq20 | hq20
            · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
          have hw3 : (64064721/2500000000000:ℝ) ≤ wfun (x + y) := wc_799 (x + y) (by linarith) (by linarith)
          have hw5 : (42660549/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1233 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total y (3081/1024:ℝ) with hc | hc
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total z (267/256:ℝ) with hc | hc
              · rcases le_total y (6131/2048:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                  have hw1 : (137922559/2500000000000:ℝ) ≤ wfun y := wc_316 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                  have hw3 : (273038177/10000000000000:ℝ) ≤ wfun (x + y) := wc_796 (x + y) (by linarith) (by linarith)
                  have hw5 : (699094733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1411 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                  have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (3:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_322 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
                  have hw3 : (170103471/2500000000000:ℝ) ≤ wfun (x + y) := wc_836 (x + y) (by linarith) (by linarith)
                  have hw4 : (1432423/10000000000000:ℝ) ≤ wfun (y + z) := wc_718 (y + z) (by linarith) (by linarith)
                  have hw5 : (1149129417/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1482 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (3:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_317 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
                have hw3 : (134503623/5000000000000:ℝ) ≤ wfun (x + y) := wc_797 (x + y) (by linarith) (by linarith)
                have hw4 : (999363/625000000000:ℝ) ≤ wfun (y + z) := wc_743 (y + z) (by linarith) (by linarith)
                have hw5 : (641911203/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1488 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_107 x (by linarith) (by linarith)
              have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (3:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_317 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_326 y (by linarith) (by linarith))
              have hw3 : (32774279/400000000000:ℝ) ≤ wfun (x + y) := wc_853 (x + y) (by linarith) (by linarith)
              have hw5 : (252901217/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1489 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
            have hw3 : (1219525351/10000000000000:ℝ) ≤ wfun (x + y) := wc_956 (x + y) (by linarith) (by linarith)
            have hw4 : (7204521/625000000000:ℝ) ≤ wfun (y + z) := wc_778 (y + z) (by linarith) (by linarith)
            have hw5 : (815292227/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1497 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_108 x (by linarith) (by linarith)
        have hw3 : (1572805651/10000000000000:ℝ) ≤ wfun (x + y) := wc_1117 (x + y) (by linarith) (by linarith)
        have hw5 : (635374807/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1414 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total y (1525/512:ℝ) with hc | hc
    · rcases le_total x (141/128:ℝ) with hc | hc
      · rcases le_total z (141/128:ℝ) with hc | hc
        · rcases le_total y (3019/1024:ℝ) with hc | hc
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
            have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_291 y (by linarith) (by linarith)
            have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_103 z (by linarith) (by linarith)
            have hw5 : (14726831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1282 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total z (277/256:ℝ) with hc | hc
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                have hw1 : (67339097/500000000000:ℝ) ≤ wfun y := wc_299 y (by linarith) (by linarith)
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_102 z (by linarith) (by linarith)
                have hw5 : (936576257/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1457 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_102 x (by linarith) (by linarith)
                have hw1 : (67339097/500000000000:ℝ) ≤ wfun y := wc_299 y (by linarith) (by linarith)
                have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_107 z (by linarith) (by linarith)
                have hw4 : (92147329/10000000000000:ℝ) ≤ wfun (y + z) := wc_773 (y + z) (by linarith) (by linarith)
                have hw5 : (1604867299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1494 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_107 x (by linarith) (by linarith)
              have hw1 : (67339097/500000000000:ℝ) ≤ wfun y := wc_299 y (by linarith) (by linarith)
              have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_103 z (by linarith) (by linarith)
              have hw3 : (92147329/10000000000000:ℝ) ≤ wfun (x + y) := wc_773 (x + y) (by linarith) (by linarith)
              have hw5 : (1580761433/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1495 (x + y + z) (by linarith) (by linarith)
              linarith
        · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_103 x (by linarith) (by linarith)
          have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_292 y (by linarith) (by linarith)
          have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_108 z (by linarith) (by linarith)
          have hw4 : (1440757/2000000000000:ℝ) ≤ wfun (y + z) := wc_729 (y + z) (by linarith) (by linarith)
          have hw5 : (1153447231/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1485 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_108 x (by linarith) (by linarith)
        have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_292 y (by linarith) (by linarith)
        have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_104 z (by linarith) (by linarith)
        have hw3 : (1440757/2000000000000:ℝ) ≤ wfun (x + y) := wc_729 (x + y) (by linarith) (by linarith)
        have hw5 : (563934301/5000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_1486 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_1504 (x + y + z) (by linarith) (by linarith))
        linarith
    · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_104 x (by linarith) (by linarith)
      have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_104 z (by linarith) (by linarith)
      have hw3 : (246785359/10000000000000:ℝ) ≤ wfun (x + y) := wc_800 (x + y) (by linarith) (by linarith)
      have hw4 : (246785359/10000000000000:ℝ) ≤ wfun (y + z) := wc_800 (y + z) (by linarith) (by linarith)
      have hw5 : (96139667/500000000000:ℝ) ≤ wfun (x + y + z) := by
        rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
        · exact le_trans (by norm_num) (wc_1499 (x + y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_1508 (x + y + z) (by linarith) (by linarith))
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_209 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (179/64:ℝ) ≤ y) (hy2 : y ≤ (105/32:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (141/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (389/128:ℝ) with hc | hc
  · rcases le_total z (131/64:ℝ) with hc | hc
    · rcases le_total y (747/256:ℝ) with hc | hc
      · have hw1 : (1457053011/2000000000000:ℝ) ≤ wfun y := wc_287 y (by linarith) (by linarith)
        have hw4 : (498772193/10000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (19/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_1208 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_1209 (y + z) (by linarith) (by linarith))
        linarith
      · rcases le_total x (17/16:ℝ) with hc | hc
        · rcases le_total z (63/32:ℝ) with hc | hc
          · have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_117 z (by linarith) (by linarith)
            have hw4 : (533121/1000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (5:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_1211 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_1212 (y + z) (by linarith) (by linarith))
            linarith
          · linarith
        · linarith
    · linarith
  · linarith

end Zeta23Ext.Bridge.FourPoint
