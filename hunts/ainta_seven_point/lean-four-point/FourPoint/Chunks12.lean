import FourPoint.Cells

/-! Chunk module 12 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_42 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (529/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1073/1024:ℝ) with hc | hc
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · rcases le_total z (1053/1024:ℝ) with hc | hc
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
        have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
        have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
        have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
        have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_802 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
        have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
        have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
        have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_813 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (1053/1024:ℝ) with hc | hc
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
        have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
        have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
        have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_813 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
          have hw3 : (7141617/2500000000000:ℝ) ≤ wfun (x + y) := wc_420 (x + y) (by linarith) (by linarith)
          have hw5 : (323709737/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_822 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
          have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
          have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
          have hw3 : (27892031/5000000000000:ℝ) ≤ wfun (x + y) := wc_452 (x + y) (by linarith) (by linarith)
          have hw5 : (728663451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_841 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · rcases le_total z (1053/1024:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
        have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
        have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
        have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
        have hw4 : (28217469/5000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
        have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_813 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
        have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
        have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
        have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_823 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (1053/1024:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
        have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
        have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
        have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_823 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
        have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
        have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_850 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_44 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (1063/1024:ℝ) ≤ z) (hz2 : z ≤ (267/256:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (4057/2048:ℝ) with hc | hc
  · rcases le_total z (2131/2048:ℝ) with hc | hc
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
          have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
          have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
          have hw5 : (820415059/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_845 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
          have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
          have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
          have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
          have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
          have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
          have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
          have hw5 : (865374359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
            have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
            have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
            have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_359 (x + y) (by linarith) (by linarith)
            have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
              have hw5 : (192091031/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_864 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
              have hw5 : (984546007/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_868 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
              have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
                have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
            have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
            have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
              have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
              have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
                have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
              have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
              have hw5 : (5167889/50000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
                have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
                have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total z (2131/2048:ℝ) with hc | hc
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
          have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_24 z (by linarith) (by linarith)
          have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_387 (x + y) (by linarith) (by linarith)
          have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_858 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
            have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
            have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_403 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4257/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (2586175977/10000000000000:ℝ) ≤ wfun z := wc_23 z (by linarith) (by linarith)
            have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (126039153/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
            have hw2 : (560227329/2500000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_417 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
            have hw5 : (1057880619/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
              have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
              have hw5 : (5167889/50000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
                have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
                have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
                have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
                have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (264629371/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_886 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
              have hw5 : (33866839/312500000000:ℝ) ≤ wfun (x + y + z) := wc_892 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
                have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
                have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
                have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
                have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_402 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
              have hw5 : (264629371/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_886 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_179 y (by linarith) (by linarith)
              have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
              have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_410 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
              have hw5 : (33866839/312500000000:ℝ) ≤ wfun (x + y + z) := wc_892 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_34 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
                have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                  have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                  have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                  have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                  have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                  have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                  have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_409 (x + y) (by linarith) (by linarith)
                  have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                  have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                  have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                  have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                  have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                  have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (4267/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
                have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
                have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
                have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (1921155551/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
                have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                  have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                  have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                  have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                  have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                  have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                  have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                  have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                  have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                  have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                  have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                  have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                  have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (8539/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                  have hw2 : (1770787537/10000000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                  have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                  have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_35 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                  have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                  have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                  linarith

set_option maxHeartbeats 20000000 in
lemma ch_50 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (529/512:ℝ) ≤ z) (hz2 : z ≤ (1063/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (2151/2048:ℝ) with hc | hc
  · rcases le_total y (4057/2048:ℝ) with hc | hc
    · rcases le_total z (2121/2048:ℝ) with hc | hc
      · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
        have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
        have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
        have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_419 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
        have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
          have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_418 (x + y) (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
          have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
          have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_436 (x + y) (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
          have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_867 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total z (2121/2048:ℝ) with hc | hc
      · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
        have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
        have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
        have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
        have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
        have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_70 x (by linarith) (by linarith)
          have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (28027757/5000000000000:ℝ) ≤ wfun (x + y) := wc_450 (x + y) (by linarith) (by linarith)
          have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_873 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
          have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
          have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
          have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_466 (x + y) (by linarith) (by linarith)
          have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_889 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total y (4057/2048:ℝ) with hc | hc
    · rcases le_total z (2121/2048:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
        have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
        have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
        have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_339 (y + z) (by linarith) (by linarith)
        have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
        have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_163 y (by linarith) (by linarith)
        have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
        have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_451 (x + y) (by linarith) (by linarith)
        have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
        have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (2121/2048:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
        have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
        have hw2 : (1888462017/5000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
        have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
        have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
        have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
        have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_180 y (by linarith) (by linarith)
        have hw2 : (2957142633/10000000000000:ℝ) ≤ wfun z := wc_21 z (by linarith) (by linarith)
        have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
        have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_899 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_57 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
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
  · rcases le_total x (4277/4096:ℝ) with hc | hc
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
          have hw5 : (410702219/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_844 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
          have hw5 : (866417641/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_854 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
          have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
          have hw5 : (866417641/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_854 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
          have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_348 (y + z) (by linarith) (by linarith)
          have hw5 : (866417641/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_854 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
          have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
          have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
          have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
          have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw5 : (192091031/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_864 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw5 : (984546007/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_868 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total x (4277/4096:ℝ) with hc | hc
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
          have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
          have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
          have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
          have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (268673/10000000000000:ℝ) ≤ wfun (x + y) := wc_349 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (192091031/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_864 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (984546007/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_868 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (268673/10000000000000:ℝ) ≤ wfun (x + y) := wc_349 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
            have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (268673/10000000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (268673/10000000000000:ℝ) ≤ wfun (x + y) := wc_349 (x + y) (by linarith) (by linarith)
            have hw5 : (192091031/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_864 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw5 : (984546007/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_868 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (268673/10000000000000:ℝ) ≤ wfun (x + y) := wc_349 (x + y) (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_353 (y + z) (by linarith) (by linarith)
            have hw5 : (5167889/50000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (1009528097/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_869 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
              have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw4 : (329/10000000000000:ℝ) ≤ wfun (y + z) := wc_352 (y + z) (by linarith) (by linarith)
              have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (153341/5000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_64 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (4047/2048:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (2151/2048:ℝ) with hc | hc
  · rcases le_total x (4277/4096:ℝ) with hc | hc
    · rcases le_total y (8099/4096:ℝ) with hc | hc
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · rcases le_total y (16193/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16193/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · rcases le_total y (16193/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16193/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (8099/4096:ℝ) with hc | hc
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16193/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16193/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16193/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16193/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17113/16384:ℝ) with hc | hc
                · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (2641873/10000000000000:ℝ) ≤ wfun (x + y) := wc_367 (x + y) (by linarith) (by linarith)
                  have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                  have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (716733/2000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
                  have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                  have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (2641873/10000000000000:ℝ) ≤ wfun (x + y) := wc_367 (x + y) (by linarith) (by linarith)
                  have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                  have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (716733/2000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
                  have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                  have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (2641873/10000000000000:ℝ) ≤ wfun (x + y) := wc_367 (x + y) (by linarith) (by linarith)
                  have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                  have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (716733/2000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
                  have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                  have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
                  have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                  have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
                  have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                  have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
                  have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
                  have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                  have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                  have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
                  have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                  have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                  have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                  have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
                  have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                  have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total x (4277/4096:ℝ) with hc | hc
    · rcases le_total y (8099/4096:ℝ) with hc | hc
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_938 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
          have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_946 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
            have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_945 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
              have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
            have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (153341/5000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
            have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
            have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_980 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (8099/4096:ℝ) with hc | hc
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16193/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16193/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
            have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_150 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (153341/5000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
            have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_435 (y + z) (by linarith) (by linarith)
            have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_980 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_442 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_434 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8609/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (2426501/500000000000:ℝ) ≤ wfun (y + z) := wc_441 (y + z) (by linarith) (by linarith)
                have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
                have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_155 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
            have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_449 (y + z) (by linarith) (by linarith)
            have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (16203/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
              have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
              have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_75 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
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
  · rcases le_total x (4297/4096:ℝ) with hc | hc
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (1214778741/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_921 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
              have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (253929443/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1297131539/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_944 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
              have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_954 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
                have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_70 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (4297/4096:ℝ) with hc | hc
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_964 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16173/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5782371603/10000000000000:ℝ) ≤ wfun y := wc_141 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_979 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5654284063/10000000000000:ℝ) ≤ wfun y := wc_145 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_369 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1001 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_988 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1000 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1010 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1034 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (8089/4096:ℝ) with hc | hc
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_373 (x + y) (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_989 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_380 (x + y) (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1001 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_79 x (by linarith) (by linarith)
          have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
          have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
          have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1011 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16183/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (221106819/400000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (5402529921/10000000000000:ℝ) ≤ wfun y := wc_148 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_386 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_147 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_396 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1055 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_82 (x y z : ℝ) (hx1 : (4277/4096:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (4057/2048:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (8109/4096:ℝ) with hc | hc
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8559/8192:ℝ) with hc | hc
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
            have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (245935877/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_932 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                have hw5 : (245935877/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_932 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8559/8192:ℝ) with hc | hc
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (628193277/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_940 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16213/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (7269931/10000000000000:ℝ) ≤ wfun (x + y) := wc_377 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32421/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (60732327/125000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4391993/5000000000000:ℝ) ≤ wfun (x + y) := wc_381 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4799854363/10000000000000:ℝ) ≤ wfun y := wc_166 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32431/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2370744759/5000000000000:ℝ) ≤ wfun y := wc_167 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2341745747/5000000000000:ℝ) ≤ wfun y := wc_169 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total z (4287/4096:ℝ) with hc | hc
    · rcases le_total x (8559/8192:ℝ) with hc | hc
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (621406689/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_935 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8569/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8559/8192:ℝ) with hc | hc
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1284126783/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17113/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16223/8192:ℝ) with hc | hc
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1297911731/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_951 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1311765751/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_958 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32441/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8579/8192:ℝ) with hc | hc
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (17153/16384:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                  have hw2 : (168496229/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                  have hw4 : (2378669/625000000000:ℝ) ≤ wfun (y + z) := wc_429 (y + z) (by linarith) (by linarith)
                  have hw5 : (338537097/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_975 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                  have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_64 z (by linarith) (by linarith)
                  have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                  have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                  have hw5 : (171035259/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_981 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (17123/16384:ℝ) with hc | hc
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32451/16384:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_119 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (4057/2048:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (2151/2048:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4287/4096:ℝ) with hc | hc
  · rcases le_total y (8119/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_434 (x + y) (by linarith) (by linarith)
          have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
          have hw5 : (335458679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1101 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_442 (x + y) (by linarith) (by linarith)
          have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
          have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total y (8119/4096:ℝ) with hc | hc
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16233/8192:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (4307/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · rcases le_total z (8609/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (31733701/1000000000000:ℝ) ≤ wfun z := wc_84 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_87 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16243/8192:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
            have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
            have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
            have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
          have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
          have hw5 : (43501511/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1120 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
          have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_187 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
          have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
          have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_129 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (8129/4096:ℝ) ≤ y) (hy2 : y ≤ (4067/2048:ℝ))
    (hz1 : (2141/2048:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (4287/4096:ℝ) with hc | hc
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16263/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32531/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3651040643/10000000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3600349479/10000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32531/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3651040643/10000000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3600349479/10000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32531/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3651040643/10000000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3600349479/10000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32531/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3651040643/10000000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3600349479/10000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16263/8192:ℝ) with hc | hc
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
              have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
              have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8569/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32531/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3651040643/10000000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3600349479/10000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32531/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3651040643/10000000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
              have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3600349479/10000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
              have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
              have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
              have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32531/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3651040643/10000000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3600349479/10000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32531/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3651040643/10000000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3600349479/10000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
              have hw3 : (103298437/10000000000000:ℝ) ≤ wfun (x + y) := wc_496 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16263/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
              have hw4 : (20651327/2000000000000:ℝ) ≤ wfun (y + z) := wc_497 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (108727819/10000000000000:ℝ) ≤ wfun (y + z) := wc_501 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
              have hw4 : (20651327/2000000000000:ℝ) ≤ wfun (y + z) := wc_497 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (108727819/10000000000000:ℝ) ≤ wfun (y + z) := wc_501 (y + z) (by linarith) (by linarith)
              have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
            have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
            have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
            have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
            have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
            have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
            have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
            have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
            have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (16263/8192:ℝ) with hc | hc
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
              have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
              have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
              have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
              have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
              have hw4 : (20651327/2000000000000:ℝ) ≤ wfun (y + z) := wc_497 (y + z) (by linarith) (by linarith)
              have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (108727819/10000000000000:ℝ) ≤ wfun (y + z) := wc_501 (y + z) (by linarith) (by linarith)
              have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32521/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3753514923/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
              have hw4 : (20651327/2000000000000:ℝ) ≤ wfun (y + z) := wc_497 (y + z) (by linarith) (by linarith)
              have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (3702095739/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
              have hw4 : (108727819/10000000000000:ℝ) ≤ wfun (y + z) := wc_501 (y + z) (by linarith) (by linarith)
              have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8579/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
            have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
            have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
            have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
            have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
            have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
            have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
            have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
            have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
            have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_131 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (4067/2048:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (2141/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4287/4096:ℝ) with hc | hc
  · rcases le_total y (8139/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (8139/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
              have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (57169429/5000000000000:ℝ) ≤ wfun (x + y) := wc_503 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (60044823/5000000000000:ℝ) ≤ wfun (x + y) := wc_508 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16273/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (62990037/5000000000000:ℝ) ≤ wfun (x + y) := wc_509 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (66005017/5000000000000:ℝ) ≤ wfun (x + y) := wc_512 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
              have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
            have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
            have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16283/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_133 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (4067/2048:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (2151/2048:ℝ) with hc | hc
  · rcases le_total x (4277/4096:ℝ) with hc | hc
    · rcases le_total y (8129/4096:ℝ) with hc | hc
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1467812531/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1032 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17103/16384:ℝ) with hc | hc
                · have hw0 : (1422414083/10000000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
                  have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                  have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
                  have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                  have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (17103/16384:ℝ) with hc | hc
                · have hw0 : (1422414083/10000000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17103/16384:ℝ) with hc | hc
                · have hw0 : (1422414083/10000000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
              have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · rcases le_total y (16263/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (748607759/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1041 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16263/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · rcases le_total y (16263/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
              have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
              have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16263/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
              have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (8129/4096:ℝ) with hc | hc
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17113/16384:ℝ) with hc | hc
                · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
                  have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                  have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (32501/16384:ℝ) with hc | hc
                  · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                    have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                    have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                    have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                    have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                    have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                    have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                    have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                    have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                    have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                    have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (17113/16384:ℝ) with hc | hc
                · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17113/16384:ℝ) with hc | hc
                · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (17113/16384:ℝ) with hc | hc
                · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · rcases le_total y (32501/16384:ℝ) with hc | hc
                  · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                    have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                    have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                    have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                    have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                    have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                    have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                    have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                    have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                    have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                    have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total y (32501/16384:ℝ) with hc | hc
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                    have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                    have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                    have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                    have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                    have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                    have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                    have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                    have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                    have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                    have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                  have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                  have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4297/4096:ℝ) with hc | hc
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16263/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17113/16384:ℝ) with hc | hc
                · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16263/8192:ℝ) with hc | hc
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
                  have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                  have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                  have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
                  have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                  have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total z (8589/8192:ℝ) with hc | hc
              · rcases le_total x (17123/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                  have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                  have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                  have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16263/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (16418259/1000000000000:ℝ) ≤ wfun (y + z) := wc_521 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16263/8192:ℝ) with hc | hc
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
                have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8599/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                have hw4 : (16418259/1000000000000:ℝ) ≤ wfun (y + z) := wc_521 (y + z) (by linarith) (by linarith)
                have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total x (4277/4096:ℝ) with hc | hc
    · rcases le_total y (8129/4096:ℝ) with hc | hc
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
              have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
              have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
              have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_427 (x + y) (by linarith) (by linarith)
              have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
              have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
              have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_416 (x + y) (by linarith) (by linarith)
            have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_428 (x + y) (by linarith) (by linarith)
            have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8549/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
            have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_434 (x + y) (by linarith) (by linarith)
            have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (16263/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
              have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
              linarith
        · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
          have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_435 (x + y) (by linarith) (by linarith)
          have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
          have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (8129/4096:ℝ) with hc | hc
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_433 (x + y) (by linarith) (by linarith)
              have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
              have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16253/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
              have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
              have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_434 (x + y) (by linarith) (by linarith)
            have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (335458679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1101 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_442 (x + y) (by linarith) (by linarith)
            have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4307/4096:ℝ) with hc | hc
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · rcases le_total y (16263/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
              have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
              have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16263/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
              have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_85 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
              have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8559/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
            have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
            have hw5 : (43501511/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1120 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_458 (x + y) (by linarith) (by linarith)
            have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
            have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_143 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (4297/4096:ℝ))
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
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
            have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
            have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total z (4277/4096:ℝ) with hc | hc
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8549/8192:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8589/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17173/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (653599921/10000000000000:ℝ) ≤ wfun x := wc_68 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_73 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                have hw4 : (8706009/2500000000000:ℝ) ≤ wfun (y + z) := wc_426 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (38043279/10000000000000:ℝ) ≤ wfun (y + z) := wc_430 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8559/8192:ℝ) with hc | hc
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17183/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (92771811/10000000000000:ℝ) ≤ wfun (x + y) := wc_475 (x + y) (by linarith) (by linarith)
                have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (568299723/10000000000000:ℝ) ≤ wfun x := wc_74 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (97965061/10000000000000:ℝ) ≤ wfun (x + y) := wc_494 (x + y) (by linarith) (by linarith)
                have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_76 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_179 (x y z : ℝ) (hx1 : (539/512:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (1023/512:ℝ) with hc | hc
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_92 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                    have hw3 : (326592691/10000000000000:ℝ) ≤ wfun (x + y) := wc_551 (x + y) (by linarith) (by linarith)
                    have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                    have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1147 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_95 x (by linarith) (by linarith)
                    have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                    have hw3 : (365741913/10000000000000:ℝ) ≤ wfun (x + y) := wc_559 (x + y) (by linarith) (by linarith)
                    have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_481 (y + z) (by linarith) (by linarith)
                    have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1160 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
                  have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                  have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                  have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                  have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_517 (y + z) (by linarith) (by linarith)
                  have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                  have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                  have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                  have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_482 (y + z) (by linarith) (by linarith)
                have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1165 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_562 (x + y) (by linarith) (by linarith)
                have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_518 (y + z) (by linarith) (by linarith)
                have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1170 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
                  have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_531 (y + z) (by linarith) (by linarith)
                  have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
                  have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_544 (y + z) (by linarith) (by linarith)
                  have hw5 : (1171101043/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1175 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_560 (x + y) (by linarith) (by linarith)
                have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_545 (y + z) (by linarith) (by linarith)
                have hw5 : (2336612903/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1176 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
              have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_561 (x + y) (by linarith) (by linarith)
              have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_533 (y + z) (by linarith) (by linarith)
              have hw5 : (291380049/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1177 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4087/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_229 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_562 (x + y) (by linarith) (by linarith)
                have hw4 : (7636599/400000000000:ℝ) ≤ wfun (y + z) := wc_532 (y + z) (by linarith) (by linarith)
                have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1170 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_232 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (148228771/2500000000000:ℝ) ≤ wfun (x + y) := wc_566 (x + y) (by linarith) (by linarith)
                have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_545 (y + z) (by linarith) (by linarith)
                have hw5 : (2336612903/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1176 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_567 (x + y) (by linarith) (by linarith)
              have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_533 (y + z) (by linarith) (by linarith)
              have hw5 : (291380049/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1177 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
            have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
            have hw5 : (3861047/15625000000:ℝ) ≤ wfun (x + y + z) := wc_1179 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_483 (y + z) (by linarith) (by linarith)
            have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1172 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
            have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_533 (y + z) (by linarith) (by linarith)
            have hw5 : (3861047/15625000000:ℝ) ≤ wfun (x + y + z) := wc_1179 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_534 (y + z) (by linarith) (by linarith)
          have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1180 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
          have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_555 (y + z) (by linarith) (by linarith)
          have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1180 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_564 (x + y) (by linarith) (by linarith)
          have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
          have hw5 : (690206739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1190 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
        have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
        have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_565 (x + y) (by linarith) (by linarith)
        have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
        have hw5 : (549546581/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1191 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2051/1024:ℝ) with hc | hc
        · have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_570 (x + y) (by linarith) (by linarith)
          have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_555 (y + z) (by linarith) (by linarith)
          have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1180 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
          have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_580 (x + y) (by linarith) (by linarith)
          have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
          have hw5 : (690206739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1190 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_41 z (by linarith) (by linarith)
        have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_581 (x + y) (by linarith) (by linarith)
        have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_556 (y + z) (by linarith) (by linarith)
        have hw5 : (549546581/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1191 (x + y + z) (by linarith) (by linarith)
        linarith
    · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
        rcases le_total y (2:ℝ) with hq10 | hq10
        · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_572 (x + y) (by linarith) (by linarith)
      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
      have hw5 : (3048526697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1193 (x + y + z) (by linarith) (by linarith)
      linarith

end Zeta23Ext.Bridge.FourPoint
