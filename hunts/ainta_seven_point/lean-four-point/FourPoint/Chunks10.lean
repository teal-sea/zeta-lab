import FourPoint.Cells

/-! Chunk module 10 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_14 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (529/512:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1063/1024:ℝ) with hc | hc
  · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
    have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
    have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
    have hw5 : (165310021/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_782 (x + y + z) (by linarith) (by linarith)
    linarith
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
      have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_164 y (by linarith) (by linarith)
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_330 (y + z) (by linarith) (by linarith)
      have hw5 : (128356097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_795 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total z (1053/1024:ℝ) with hc | hc
      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
        have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
        have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
        have hw5 : (184146301/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_802 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_15 z (by linarith) (by linarith)
        have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
        have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_813 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_22 (x y z : ℝ) (hx1 : (2131/2048:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (4057/2048:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (2141/2048:ℝ) with hc | hc
  · rcases le_total x (4267/4096:ℝ) with hc | hc
    · rcases le_total y (8109/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
          have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
          have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
          have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
          have hw5 : (3564753/39062500000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
          have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
          have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
          have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
          have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
          have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
          have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
          have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
          have hw5 : (959876941/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (8529/8192:ℝ) with hc | hc
          · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (153341/5000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (5167889/50000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (8109/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8539/8192:ℝ) with hc | hc
          · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
            have hw5 : (192091031/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_864 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (153341/5000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_359 (y + z) (by linarith) (by linarith)
            have hw5 : (984546007/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_868 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8539/8192:ℝ) with hc | hc
          · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8539/8192:ℝ) with hc | hc
          · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
            have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
              have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8539/8192:ℝ) with hc | hc
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (4267/4096:ℝ) with hc | hc
    · rcases le_total y (8109/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8529/8192:ℝ) with hc | hc
          · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (1008920431/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_870 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_387 (y + z) (by linarith) (by linarith)
            have hw5 : (5167889/50000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8529/8192:ℝ) with hc | hc
          · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (264629371/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_886 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_162 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (33866839/312500000000:ℝ) ≤ wfun (x + y + z) := wc_892 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8529/8192:ℝ) with hc | hc
          · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_403 (y + z) (by linarith) (by linarith)
            have hw5 : (264629371/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_886 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8529/8192:ℝ) with hc | hc
          · have hw0 : (1038927507/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
            have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_352 (x + y) (by linarith) (by linarith)
            have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_417 (y + z) (by linarith) (by linarith)
            have hw5 : (554620627/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_895 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (8109/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8539/8192:ℝ) with hc | hc
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_386 (y + z) (by linarith) (by linarith)
              have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_396 (y + z) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8539/8192:ℝ) with hc | hc
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16213/8192:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (306931/10000000000000:ℝ) ≤ wfun (x + y) := wc_355 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8539/8192:ℝ) with hc | hc
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_402 (y + z) (by linarith) (by linarith)
              have hw5 : (1109908939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
              have hw5 : (567853581/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_903 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
                have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8539/8192:ℝ) with hc | hc
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
              have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_416 (y + z) (by linarith) (by linarith)
              have hw5 : (145223163/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1770787537/10000000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_428 (y + z) (by linarith) (by linarith)
              have hw5 : (594071357/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16223/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                have hw5 : (47554307/400000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
                have hw5 : (1215509621/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_920 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
                have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
                have hw5 : (155304961/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_936 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_38 (x y z : ℝ) (hx1 : (529/512:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (1023/512:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (539/512:ℝ) with hc | hc
  · rcases le_total x (1063/1024:ℝ) with hc | hc
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · rcases le_total z (1073/1024:ℝ) with hc | hc
        · rcases le_total x (2121/2048:ℝ) with hc | hc
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (22987523/2500000000000:ℝ) ≤ wfun (x + y) := wc_482 (x + y) (by linarith) (by linarith)
            have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
            have hw5 : (1424080951/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1016 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
              have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_553 (y + z) (by linarith) (by linarith)
              have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1069 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_237 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
              have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_561 (y + z) (by linarith) (by linarith)
              have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1106 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (2121/2048:ℝ) with hc | hc
          · have hw0 : (1888462017/5000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (22987523/2500000000000:ℝ) ≤ wfun (x + y) := wc_482 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
            have hw5 : (66491401/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1107 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_518 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
            have hw5 : (1787757479/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1135 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (1073/1024:ℝ) with hc | hc
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
          have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
          have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1108 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
          have hw4 : (694482783/10000000000000:ℝ) ≤ wfun (y + z) := wc_570 (y + z) (by linarith) (by linarith)
          have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1151 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · rcases le_total z (1073/1024:ℝ) with hc | hc
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · rcases le_total z (2141/2048:ℝ) with hc | hc
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
                have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
                have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1105 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
                have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_560 (y + z) (by linarith) (by linarith)
                have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1133 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_237 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
              have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_561 (y + z) (by linarith) (by linarith)
              have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1134 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · rcases le_total z (2141/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_39 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
                have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
                have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1133 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_56 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
                have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_560 (y + z) (by linarith) (by linarith)
                have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1148 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_237 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
              have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_561 (y + z) (by linarith) (by linarith)
              have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1149 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_532 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
            have hw5 : (1917416231/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1150 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
              have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_234 y (by linarith) (by linarith))
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
              have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
              have hw4 : (493784853/10000000000000:ℝ) ≤ wfun (y + z) := wc_563 (y + z) (by linarith) (by linarith)
              have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1165 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_237 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
              have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_552 (x + y) (by linarith) (by linarith)
              have hw4 : (295506067/5000000000000:ℝ) ≤ wfun (y + z) := wc_567 (y + z) (by linarith) (by linarith)
              have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1170 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (1073/1024:ℝ) with hc | hc
        · rcases le_total x (2131/2048:ℝ) with hc | hc
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_553 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
            have hw5 : (1917416231/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1150 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_561 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
            have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1166 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
          have hw4 : (694482783/10000000000000:ℝ) ≤ wfun (y + z) := wc_570 (y + z) (by linarith) (by linarith)
          have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1172 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total x (1063/1024:ℝ) with hc | hc
    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
        rcases le_total y (2:ℝ) with hq10 | hq10
        · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
      have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_484 (x + y) (by linarith) (by linarith)
      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_572 (y + z) (by linarith) (by linarith)
      have hw5 : (947330549/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1153 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
        have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
        have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
        have hw4 : (172511147/2500000000000:ℝ) ≤ wfun (y + z) := wc_571 (y + z) (by linarith) (by linarith)
        have hw5 : (271686247/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1173 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
        have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
        have hw4 : (924357731/10000000000000:ℝ) ≤ wfun (y + z) := wc_581 (y + z) (by linarith) (by linarith)
        have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1180 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_67 (x y z : ℝ) (hx1 : (4287/4096:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
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
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (158753629/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_942 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1283740729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_950 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4668509/10000000000000:ℝ) ≤ wfun (x + y) := wc_371 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (737039/1250000000000:ℝ) ≤ wfun (x + y) := wc_376 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (648760781/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_952 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1311371447/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_959 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1325290301/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_962 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (669639019/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_974 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1324891991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_963 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1367459827/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_983 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16193/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
            have hw5 : (1352927899/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_978 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (5278861443/10000000000000:ℝ) ≤ wfun y := wc_149 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            have hw5 : (690619293/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_987 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (2578332043/5000000000000:ℝ) ≤ wfun y := wc_152 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
            have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
            have hw5 : (1409823377/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_999 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (4297/4096:ℝ) with hc | hc
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (5220389/5000000000000:ℝ) ≤ wfun (x + y) := wc_383 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (33142219/250000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (1339680673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_973 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (23354711/10000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
              have hw5 : (84583411/625000000000:ℝ) ≤ wfun (x + y + z) := wc_977 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (12240211/10000000000000:ℝ) ≤ wfun (x + y) := wc_391 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (676870703/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_976 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                have hw5 : (170983859/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_982 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14182191/10000000000000:ℝ) ≤ wfun (x + y) := wc_393 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32401/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (5097185467/10000000000000:ℝ) ≤ wfun y := wc_153 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (2518492283/5000000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (2920523/1250000000000:ℝ) ≤ wfun (y + z) := wc_408 (y + z) (by linarith) (by linarith)
                have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (26016381/10000000000000:ℝ) ≤ wfun (y + z) := wc_412 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32411/16384:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (4977151133/10000000000000:ℝ) ≤ wfun y := wc_157 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                have hw4 : (3601311/1250000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
                have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (61471063/125000000000:ℝ) ≤ wfun y := wc_159 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                have hw4 : (6349281/2000000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8579/8192:ℝ) with hc | hc
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1381653711/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_986 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1395916139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_995 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17153/16384:ℝ) with hc | hc
            · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16203/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (1410247029/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_998 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
              have hw4 : (28798809/10000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
              have hw5 : (356161573/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1004 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (2517968433/5000000000000:ℝ) ≤ wfun y := wc_154 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
            have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
            have hw5 : (1438681587/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1008 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
              have hw4 : (17404961/5000000000000:ℝ) ≤ wfun (y + z) := wc_427 (y + z) (by linarith) (by linarith)
              have hw5 : (726824801/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1028 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17163/16384:ℝ) with hc | hc
            · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
              have hw1 : (2458339391/5000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
              have hw4 : (20693629/5000000000000:ℝ) ≤ wfun (y + z) := wc_433 (y + z) (by linarith) (by linarith)
              have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_80 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (4057/2048:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (2141/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4277/4096:ℝ) with hc | hc
  · rcases le_total y (8109/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
            have hw5 : (1009528097/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_869 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
            have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
            have hw5 : (517100111/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (2638657/10000000000000:ℝ) ≤ wfun (y + z) := wc_369 (y + z) (by linarith) (by linarith)
            have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (1187329/10000000000000:ℝ) ≤ wfun (x + y) := wc_357 (x + y) (by linarith) (by linarith)
            have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
            have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
            have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
            have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1085044203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_890 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2640801/10000000000000:ℝ) ≤ wfun (x + y) := wc_368 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
            have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (7258139/10000000000000:ℝ) ≤ wfun (y + z) := wc_380 (y + z) (by linarith) (by linarith)
            have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
            have hw4 : (4662827/10000000000000:ℝ) ≤ wfun (y + z) := wc_373 (y + z) (by linarith) (by linarith)
            have hw5 : (13554891/125000000000:ℝ) ≤ wfun (x + y + z) := wc_891 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8549/8192:ℝ) with hc | hc
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17103/16384:ℝ) with hc | hc
              · have hw0 : (1422414083/10000000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total y (8109/4096:ℝ) with hc | hc
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
            have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (593183/5000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
            have hw5 : (264788707/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (1085044203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_890 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (1187329/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
              have hw5 : (1085044203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_890 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (2640801/10000000000000:ℝ) ≤ wfun (y + z) := wc_368 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (2333307/5000000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16213/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (227001/312500000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (7266981/10000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1162834311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_905 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_161 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (4390211/5000000000000:ℝ) ≤ wfun (x + y) := wc_382 (x + y) (by linarith) (by linarith)
                have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
                have hw5 : (1175989937/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_912 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_168 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total z (4277/4096:ℝ) with hc | hc
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (555288563/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_893 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (2333307/5000000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (1136390777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_902 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_395 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8549/8192:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
              have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_401 (x + y) (by linarith) (by linarith)
              have hw4 : (227001/312500000000:ℝ) ≤ wfun (y + z) := wc_379 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (8559/8192:ℝ) with hc | hc
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
              have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
              have hw3 : (2608077/2500000000000:ℝ) ≤ wfun (x + y) := wc_385 (x + y) (by linarith) (by linarith)
              have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
              have hw5 : (116248451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (5218271/5000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (2447049/2000000000000:ℝ) ≤ wfun (x + y) := wc_392 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17113/16384:ℝ) with hc | hc
              · have hw0 : (323505483/2500000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (4619603/2500000000000:ℝ) ≤ wfun (y + z) := wc_401 (y + z) (by linarith) (by linarith)
                have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16223/8192:ℝ) with hc | hc
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (594607679/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_913 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (650401/400000000000:ℝ) ≤ wfun (x + y) := wc_398 (x + y) (by linarith) (by linarith)
                have hw4 : (2608077/2500000000000:ℝ) ≤ wfun (y + z) := wc_385 (y + z) (by linarith) (by linarith)
                have hw5 : (37578453/312500000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (7088219/5000000000000:ℝ) ≤ wfun (x + y) := wc_394 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (32441/16384:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (16266623/10000000000000:ℝ) ≤ wfun (x + y) := wc_397 (x + y) (by linarith) (by linarith)
                  have hw4 : (7088219/5000000000000:ℝ) ≤ wfun (y + z) := wc_394 (y + z) (by linarith) (by linarith)
                  have hw5 : (245935877/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_932 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                  have hw4 : (650401/400000000000:ℝ) ≤ wfun (y + z) := wc_398 (y + z) (by linarith) (by linarith)
                  have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (8559/8192:ℝ) with hc | hc
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (1215875267/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_919 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
                have hw4 : (221417/156250000000:ℝ) ≤ wfun (y + z) := wc_395 (y + z) (by linarith) (by linarith)
                have hw5 : (307327397/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17123/16384:ℝ) with hc | hc
              · rcases le_total y (32451/16384:ℝ) with hc | hc
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
                  have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                  have hw5 : (1243187209/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (585927977/5000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                  have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                  have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                  have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32451/16384:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
                  have hw4 : (18485909/10000000000000:ℝ) ≤ wfun (y + z) := wc_400 (y + z) (by linarith) (by linarith)
                  have hw5 : (1256764439/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_939 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
                  have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
                  have hw4 : (10426997/5000000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
                  have hw5 : (1270410991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_941 (x + y + z) (by linarith) (by linarith)
                  linarith

set_option maxHeartbeats 20000000 in
lemma ch_113 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
    (hy1 : (8109/4096:ℝ) ≤ y) (hy2 : y ≤ (4057/2048:ℝ))
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
    · rcases le_total y (16223/8192:ℝ) with hc | hc
      · rcases le_total z (8589/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32441/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (1382068991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_985 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32441/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (55853427/400000000000:ℝ) ≤ wfun (x + y + z) := wc_994 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (22453103/5000000000000:ℝ) ≤ wfun (y + z) := wc_438 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32441/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (18493409/10000000000000:ℝ) ≤ wfun (x + y) := wc_399 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32441/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8589/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (712537199/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1003 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (16223/8192:ℝ) with hc | hc
      · rcases le_total z (8589/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32441/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (10351009/2500000000000:ℝ) ≤ wfun (y + z) := wc_432 (y + z) (by linarith) (by linarith)
              have hw5 : (1410670839/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_997 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total z (17173/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32441/16384:ℝ) with hc | hc
            · rcases le_total z (17173/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (41420821/10000000000000:ℝ) ≤ wfun (y + z) := wc_431 (y + z) (by linarith) (by linarith)
                have hw5 : (285100533/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1002 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17173/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (4492441/1000000000000:ℝ) ≤ wfun (y + z) := wc_437 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32441/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32441/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (48549689/10000000000000:ℝ) ≤ wfun (y + z) := wc_440 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (3270899/625000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (8589/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · rcases le_total z (17173/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (1439978849/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1005 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17173/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · rcases le_total z (17173/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (6071171/1250000000000:ℝ) ≤ wfun (y + z) := wc_439 (y + z) (by linarith) (by linarith)
                have hw5 : (363630819/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1026 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (17173/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (26177797/5000000000000:ℝ) ≤ wfun (y + z) := wc_443 (y + z) (by linarith) (by linarith)
                have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total x (8569/8192:ℝ) with hc | hc
    · rcases le_total y (16223/8192:ℝ) with hc | hc
      · rcases le_total z (8599/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
            have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
            have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
            have hw5 : (287822769/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1007 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (32441/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (4172491/2000000000000:ℝ) ≤ wfun (x + y) := wc_405 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (18485909/10000000000000:ℝ) ≤ wfun (x + y) := wc_400 (x + y) (by linarith) (by linarith)
            have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
            have hw5 : (58730139/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1031 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (10426997/5000000000000:ℝ) ≤ wfun (x + y) := wc_406 (x + y) (by linarith) (by linarith)
            have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
            have hw5 : (1482925379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1037 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (8599/8192:ℝ) with hc | hc
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17133/16384:ℝ) with hc | hc
          · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
            have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
            have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
            have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
            have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (16223/8192:ℝ) with hc | hc
      · rcases le_total z (8599/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32441/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (11686831/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32441/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2312930081/5000000000000:ℝ) ≤ wfun y := wc_170 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (13013467/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
              have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4568595377/10000000000000:ℝ) ≤ wfun y := wc_173 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (2920523/1250000000000:ℝ) ≤ wfun (x + y) := wc_408 (x + y) (by linarith) (by linarith)
            have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
            have hw5 : (1497665227/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1040 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_171 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (26016381/10000000000000:ℝ) ≤ wfun (x + y) := wc_412 (x + y) (by linarith) (by linarith)
            have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
            have hw5 : (1512472933/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1049 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (8599/8192:ℝ) with hc | hc
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
              have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
              have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (32451/16384:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4511697009/10000000000000:ℝ) ≤ wfun y := wc_174 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
              have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
              have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4455164921/10000000000000:ℝ) ≤ wfun y := wc_176 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
              have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
              have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (17143/16384:ℝ) with hc | hc
          · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
            have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
            have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
            have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_175 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
            have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
            have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_117 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (4287/4096:ℝ))
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
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (719773133/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1006 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (56260189/10000000000000:ℝ) ≤ wfun (y + z) := wc_446 (y + z) (by linarith) (by linarith)
                have hw5 : (1454086357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1027 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (30163501/5000000000000:ℝ) ≤ wfun (y + z) := wc_454 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (293738917/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1030 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (1483370863/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1036 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · rcases le_total z (17173/16384:ℝ) with hc | hc
                · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                  have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                  have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                  have hw5 : (73456793/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1029 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                  have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                  have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                  have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (17173/16384:ℝ) with hc | hc
                · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                  have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                  have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                  have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                  have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                  have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                  have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · rcases le_total z (17173/16384:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                  have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                  have hw4 : (14070747/2500000000000:ℝ) ≤ wfun (y + z) := wc_445 (y + z) (by linarith) (by linarith)
                  have hw5 : (296763303/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1035 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                  have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                  have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                  have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                  have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (17173/16384:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                  have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                  have hw4 : (60351447/10000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                  have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                  have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                  have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                  have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                  have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (64534721/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · rcases le_total z (17173/16384:ℝ) with hc | hc
                · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                  have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                  have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                  have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                  have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                  have hw5 : (1498565153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1038 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                  have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                  have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                  have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                  have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · rcases le_total z (17173/16384:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                  have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                  have hw2 : (653599921/10000000000000:ℝ) ≤ wfun z := wc_68 z (by linarith) (by linarith)
                  have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                  have hw4 : (16140217/2500000000000:ℝ) ≤ wfun (y + z) := wc_455 (y + z) (by linarith) (by linarith)
                  have hw5 : (189172711/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1047 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                  have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_73 z (by linarith) (by linarith)
                  have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                  have hw4 : (68911149/10000000000000:ℝ) ≤ wfun (y + z) := wc_459 (y + z) (by linarith) (by linarith)
                  have hw5 : (1528266033/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1050 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (68883243/10000000000000:ℝ) ≤ wfun (y + z) := wc_460 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (28822173/10000000000000:ℝ) ≤ wfun (x + y) := wc_413 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (396991/125000000000:ℝ) ≤ wfun (x + y) := wc_423 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (3601311/1250000000000:ℝ) ≤ wfun (x + y) := wc_414 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (6349281/2000000000000:ℝ) ≤ wfun (x + y) := wc_424 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (1527348409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1052 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (96393223/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1058 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (16233/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (8709539/2500000000000:ℝ) ≤ wfun (x + y) := wc_425 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32461/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (175959959/400000000000:ℝ) ≤ wfun y := wc_177 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (2378669/625000000000:ℝ) ≤ wfun (x + y) := wc_429 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4343199033/10000000000000:ℝ) ≤ wfun y := wc_181 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (8706009/2500000000000:ℝ) ≤ wfun (x + y) := wc_426 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (38043279/10000000000000:ℝ) ≤ wfun (x + y) := wc_430 (x + y) (by linarith) (by linarith)
              have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32471/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2143882477/5000000000000:ℝ) ≤ wfun y := wc_182 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (4232696597/10000000000000:ℝ) ≤ wfun y := wc_184 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_183 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (4297/4096:ℝ) with hc | hc
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (749057553/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1039 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (60517089/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1048 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (41420821/10000000000000:ℝ) ≤ wfun (x + y) := wc_431 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (4492441/1000000000000:ℝ) ≤ wfun (x + y) := wc_437 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (305561427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1051 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (14674493/2000000000000:ℝ) ≤ wfun (y + z) := wc_462 (y + z) (by linarith) (by linarith)
                have hw5 : (1542754747/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1057 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (39001141/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (6071171/1250000000000:ℝ) ≤ wfun (x + y) := wc_439 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32481/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2088996909/5000000000000:ℝ) ≤ wfun y := wc_185 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (26177797/5000000000000:ℝ) ≤ wfun (x + y) := wc_443 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (2061828237/5000000000000:ℝ) ≤ wfun y := wc_188 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (8589/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (8277259/1000000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (17536657/2000000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (32491/16384:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (203484221/500000000000:ℝ) ≤ wfun y := wc_189 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (401607751/1000000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (8569/8192:ℝ) with hc | hc
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (778651161/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1061 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (314476117/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1073 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (10351009/2500000000000:ℝ) ≤ wfun (x + y) := wc_432 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (22453103/5000000000000:ℝ) ≤ wfun (x + y) := wc_438 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17133/16384:ℝ) with hc | hc
            · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_441 (x + y) (by linarith) (by linarith)
            have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (16243/8192:ℝ) with hc | hc
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
              have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (48549689/10000000000000:ℝ) ≤ wfun (x + y) := wc_440 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_186 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (3270899/625000000000:ℝ) ≤ wfun (x + y) := wc_444 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (8599/8192:ℝ) with hc | hc
          · rcases le_total x (17143/16384:ℝ) with hc | hc
            · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
              have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
              have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
              have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
            have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
            have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
            have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
            have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_135 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (4067/2048:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (2151/2048:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (4287/4096:ℝ) with hc | hc
  · rcases le_total y (8129/4096:ℝ) with hc | hc
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · rcases le_total y (32501/16384:ℝ) with hc | hc
                · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (14070747/2500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                  have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                  have hw5 : (1557769973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1060 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                  have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                  have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                  have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32501/16384:ℝ) with hc | hc
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (60351447/10000000000000:ℝ) ≤ wfun (x + y) := wc_453 (x + y) (by linarith) (by linarith)
                  have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                  have hw5 : (1572852729/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1072 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                  have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                  have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                  have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (396881567/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1075 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1602739283/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1080 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · rcases le_total y (32511/16384:ℝ) with hc | hc
                · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                  have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                  have hw4 : (20651327/2000000000000:ℝ) ≤ wfun (y + z) := wc_497 (y + z) (by linarith) (by linarith)
                  have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                  have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                  have hw4 : (108727819/10000000000000:ℝ) ≤ wfun (y + z) := wc_501 (y + z) (by linarith) (by linarith)
                  have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32511/16384:ℝ) with hc | hc
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                  have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                  have hw4 : (20651327/2000000000000:ℝ) ≤ wfun (y + z) := wc_497 (y + z) (by linarith) (by linarith)
                  have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                  have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (108727819/10000000000000:ℝ) ≤ wfun (y + z) := wc_501 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · rcases le_total y (32501/16384:ℝ) with hc | hc
                · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (16140217/2500000000000:ℝ) ≤ wfun (x + y) := wc_455 (x + y) (by linarith) (by linarith)
                  have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                  have hw5 : (397000731/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1074 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                  have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                  have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                  have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32501/16384:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (68911149/10000000000000:ℝ) ≤ wfun (x + y) := wc_459 (x + y) (by linarith) (by linarith)
                  have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                  have hw5 : (1603220471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1079 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                  have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · rcases le_total y (32511/16384:ℝ) with hc | hc
                · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                  have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (20651327/2000000000000:ℝ) ≤ wfun (y + z) := wc_497 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                  have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                  have hw4 : (108727819/10000000000000:ℝ) ≤ wfun (y + z) := wc_501 (y + z) (by linarith) (by linarith)
                  have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32511/16384:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                  have hw1 : (3857446169/10000000000000:ℝ) ≤ wfun y := wc_198 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                  have hw4 : (20651327/2000000000000:ℝ) ≤ wfun (y + z) := wc_497 (y + z) (by linarith) (by linarith)
                  have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                  have hw1 : (951324587/2500000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                  have hw4 : (108727819/10000000000000:ℝ) ≤ wfun (y + z) := wc_501 (y + z) (by linarith) (by linarith)
                  have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (56260189/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (30163501/5000000000000:ℝ) ≤ wfun (x + y) := wc_454 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (64534721/10000000000000:ℝ) ≤ wfun (x + y) := wc_456 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (68883243/10000000000000:ℝ) ≤ wfun (x + y) := wc_460 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_457 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1618019543/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1082 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1633366957/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1090 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17133/16384:ℝ) with hc | hc
              · have hw0 : (1055892761/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17143/16384:ℝ) with hc | hc
              · have hw0 : (236527239/2500000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8569/8192:ℝ) with hc | hc
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (16418259/1000000000000:ℝ) ≤ wfun (y + z) := wc_521 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_59 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (16418259/1000000000000:ℝ) ≤ wfun (y + z) := wc_521 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (8129/4096:ℝ) with hc | hc
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · rcases le_total y (32501/16384:ℝ) with hc | hc
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (73402187/10000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                  have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                  have hw5 : (1618505281/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1081 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                  have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                  have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (32501/16384:ℝ) with hc | hc
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (19508469/2500000000000:ℝ) ≤ wfun (x + y) := wc_467 (x + y) (by linarith) (by linarith)
                  have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                  have hw5 : (816928633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1089 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                  have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                  have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                  have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (824390719/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1092 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17163/16384:ℝ) with hc | hc
              · rcases le_total y (32501/16384:ℝ) with hc | hc
                · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                  have hw1 : (3962835597/10000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (82806113/10000000000000:ℝ) ≤ wfun (x + y) := wc_469 (x + y) (by linarith) (by linarith)
                  have hw4 : (92734261/10000000000000:ℝ) ≤ wfun (y + z) := wc_476 (y + z) (by linarith) (by linarith)
                  have hw5 : (1649276337/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1091 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                  have hw1 : (488744817/1250000000000:ℝ) ≤ wfun y := wc_197 y (by linarith) (by linarith)
                  have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                  have hw3 : (87718793/10000000000000:ℝ) ≤ wfun (x + y) := wc_473 (x + y) (by linarith) (by linarith)
                  have hw4 : (97925413/10000000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                  have hw5 : (332952481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1096 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (1664262897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1097 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (8277259/1000000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
                have hw3 : (17536657/2000000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (14674493/2000000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
                have hw3 : (39001141/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16253/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (4297/4096:ℝ) with hc | hc
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17153/16384:ℝ) with hc | hc
              · have hw0 : (168496229/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (92734261/10000000000000:ℝ) ≤ wfun (x + y) := wc_476 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1679811243/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1098 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_64 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (97925413/10000000000000:ℝ) ≤ wfun (x + y) := wc_495 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1695426389/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1111 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · rcases le_total x (17163/16384:ℝ) with hc | hc
              · have hw0 : (186246483/2500000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (20651327/2000000000000:ℝ) ≤ wfun (x + y) := wc_497 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (342221649/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1112 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
                have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
                have hw3 : (108727819/10000000000000:ℝ) ≤ wfun (x + y) := wc_501 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1726856719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1116 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (8589/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (3813691/62500000000:ℝ) ≤ wfun z := wc_69 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_75 z (by linarith) (by linarith)
              have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (8579/8192:ℝ) with hc | hc
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
            have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
            have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
            have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (16263/8192:ℝ) with hc | hc
          · rcases le_total z (8599/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (225854567/5000000000000:ℝ) ≤ wfun z := wc_78 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
              have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (1850748599/5000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_82 z (by linarith) (by linarith)
              have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
              have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
              have hw5 : (1806053569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1127 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
            have hw1 : (719956733/2000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_79 z (by linarith) (by linarith)
            have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
            have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
            have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_158 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (2151/2048:ℝ))
    (hy1 : (4067/2048:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
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
    · rcases le_total y (8139/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (56237401/10000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (64508587/10000000000000:ℝ) ≤ wfun (y + z) := wc_457 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · rcases le_total z (8549/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
              have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
              have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
              have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
              have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
              have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
              have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (8139/4096:ℝ) with hc | hc
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
              have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
              have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
              have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
              have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_458 (y + z) (by linarith) (by linarith)
              have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8559/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (36671379/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (20684771/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
              have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
              have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
              have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
              have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4277/4096:ℝ) with hc | hc
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
              have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_464 (y + z) (by linarith) (by linarith)
              have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (25929173/1250000000000:ℝ) ≤ wfun (x + y) := wc_535 (x + y) (by linarith) (by linarith)
              have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_472 (y + z) (by linarith) (by linarith)
              have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_465 (y + z) (by linarith) (by linarith)
            have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
              have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
              have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (25929173/1250000000000:ℝ) ≤ wfun (x + y) := wc_535 (x + y) (by linarith) (by linarith)
              have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
              have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
            have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_479 (y + z) (by linarith) (by linarith)
            have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total x (4297/4096:ℝ) with hc | hc
    · rcases le_total y (8139/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (342118997/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1113 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                have hw5 : (1806053569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1127 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8579/8192:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (396484213/5000000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1806053569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1127 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
              have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
              have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
                have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
              have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
              have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
              have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
              have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8589/8192:ℝ) with hc | hc
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
              have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
              have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_69 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
              have hw5 : (183730059/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1136 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
              have hw5 : (183730059/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1136 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_75 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
              have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
              have hw5 : (93494683/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1138 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (8139/4096:ℝ) with hc | hc
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · rcases le_total z (8569/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                have hw5 : (69685963/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1118 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
                have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                have hw5 : (1773968843/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1124 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
              have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
              have hw5 : (1772905213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1125 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
              have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
              have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
              have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
              have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
              have hw5 : (183730059/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1136 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (16273/8192:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (699904903/2000000000000:ℝ) ≤ wfun y := wc_208 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (89022727/5000000000000:ℝ) ≤ wfun (x + y) := wc_525 (x + y) (by linarith) (by linarith)
              have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
              have hw5 : (183730059/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1136 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
              have hw1 : (42508981/125000000000:ℝ) ≤ wfun y := wc_211 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
              have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
              have hw5 : (93494683/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1138 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (4287/4096:ℝ) with hc | hc
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · rcases le_total y (16283/8192:ℝ) with hc | hc
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (3303364277/10000000000000:ℝ) ≤ wfun y := wc_212 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (96231343/5000000000000:ℝ) ≤ wfun (x + y) := wc_527 (x + y) (by linarith) (by linarith)
              have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
              have hw5 : (112810679/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1128 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
              have hw1 : (641492121/2000000000000:ℝ) ≤ wfun y := wc_214 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (25929173/1250000000000:ℝ) ≤ wfun (x + y) := wc_535 (x + y) (by linarith) (by linarith)
              have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
              have hw5 : (183730059/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1136 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
            have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
            have hw5 : (1836199483/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1137 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (8599/8192:ℝ) with hc | hc
          · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_78 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (19230721/1000000000000:ℝ) ≤ wfun (x + y) := wc_528 (x + y) (by linarith) (by linarith)
            have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
            have hw5 : (1868773189/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1139 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_82 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_213 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (207265849/10000000000000:ℝ) ≤ wfun (x + y) := wc_536 (x + y) (by linarith) (by linarith)
            have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
            have hw5 : (950804677/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1144 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_172 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (2141/2048:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (2041/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (4077/2048:ℝ) with hc | hc
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8149/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1009 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1033 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8559/8192:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                  have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                  have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                  have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_505 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_506 (y + z) (by linarith) (by linarith)
              have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1043 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (8149/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (46310863/5000000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1042 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1054 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8549/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1488952289/10000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                  have hw4 : (92696731/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                  have hw5 : (11928827/78125000000:ℝ) ≤ wfun (x + y + z) := wc_1053 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                  have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                  have hw4 : (51607427/5000000000000:ℝ) ≤ wfun (y + z) := wc_498 (y + z) (by linarith) (by linarith)
                  have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (25782839/2500000000000:ℝ) ≤ wfun (y + z) := wc_499 (y + z) (by linarith) (by linarith)
                have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8559/8192:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                  have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (778417423/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1062 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                  have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                  have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8559/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1232162133/10000000000000:ℝ) ≤ wfun z := wc_47 z (by linarith) (by linarith)
                  have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                  have hw4 : (57146301/5000000000000:ℝ) ≤ wfun (y + z) := wc_504 (y + z) (by linarith) (by linarith)
                  have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                  have hw4 : (787057/62500000000:ℝ) ≤ wfun (y + z) := wc_510 (y + z) (by linarith) (by linarith)
                  have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (114200161/10000000000000:ℝ) ≤ wfun (y + z) := wc_505 (y + z) (by linarith) (by linarith)
                have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (15728411/1250000000000:ℝ) ≤ wfun (y + z) := wc_511 (y + z) (by linarith) (by linarith)
                have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8149/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (138011869/10000000000000:ℝ) ≤ wfun (y + z) := wc_514 (y + z) (by linarith) (by linarith)
                have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1063 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1077 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8569/8192:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                  have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                  have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                  have hw5 : (1587049791/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1076 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                  have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                  have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
                  have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_477 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (1616563421/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1084 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (51607427/5000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_505 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_505 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (335458679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1101 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_511 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (8149/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8569/8192:ℝ) with hc | hc
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                  have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                  have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                  have hw5 : (1617533987/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1083 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                  have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                  have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
                  have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (25739029/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1094 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · rcases le_total z (8569/8192:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (1000229897/10000000000000:ℝ) ≤ wfun z := wc_54 z (by linarith) (by linarith)
                  have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                  have hw4 : (6906177/500000000000:ℝ) ≤ wfun (y + z) := wc_513 (y + z) (by linarith) (by linarith)
                  have hw5 : (65931469/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1093 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                  have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_59 z (by linarith) (by linarith)
                  have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                  have hw4 : (15087499/1000000000000:ℝ) ≤ wfun (y + z) := wc_519 (y + z) (by linarith) (by linarith)
                  have hw5 : (52478353/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1099 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (30150607/2000000000000:ℝ) ≤ wfun (y + z) := wc_520 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (57146301/5000000000000:ℝ) ≤ wfun (x + y) := wc_504 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16293/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1556503067/5000000000000:ℝ) ≤ wfun y := wc_215 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (787057/62500000000:ℝ) ≤ wfun (x + y) := wc_510 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (377499941/1250000000000:ℝ) ≤ wfun y := wc_221 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (6906177/500000000000:ℝ) ≤ wfun (x + y) := wc_513 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (26223437/156250000000:ℝ) ≤ wfun (x + y + z) := wc_1100 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16303/8192:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (1464219713/5000000000000:ℝ) ≤ wfun y := wc_222 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (15087499/1000000000000:ℝ) ≤ wfun (x + y) := wc_519 (x + y) (by linarith) (by linarith)
                have hw4 : (82024953/5000000000000:ℝ) ≤ wfun (y + z) := wc_522 (y + z) (by linarith) (by linarith)
                have hw5 : (1709569043/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1114 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                have hw1 : (2838324453/10000000000000:ℝ) ≤ wfun y := wc_224 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
                have hw3 : (16418259/1000000000000:ℝ) ≤ wfun (x + y) := wc_521 (x + y) (by linarith) (by linarith)
                have hw4 : (35580319/2000000000000:ℝ) ≤ wfun (y + z) := wc_526 (y + z) (by linarith) (by linarith)
                have hw5 : (870552183/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1119 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (138011869/10000000000000:ℝ) ≤ wfun (x + y) := wc_514 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (43501511/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1120 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_223 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
              have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8159/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (138011869/10000000000000:ℝ) ≤ wfun (x + y) := wc_514 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
              have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1064 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
              have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1078 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (138011869/10000000000000:ℝ) ≤ wfun (x + y) := wc_514 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
            have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1086 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
            have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
            have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8159/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (82024953/5000000000000:ℝ) ≤ wfun (x + y) := wc_522 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
              have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1085 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
              have hw3 : (35580319/2000000000000:ℝ) ≤ wfun (x + y) := wc_526 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_515 (y + z) (by linarith) (by linarith)
              have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_1095 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (82024953/5000000000000:ℝ) ≤ wfun (x + y) := wc_522 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (335458679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1101 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (35580319/2000000000000:ℝ) ≤ wfun (x + y) := wc_526 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
              have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_38 z (by linarith) (by linarith)
            have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
            have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1102 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
            have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
            have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
            have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (4277/4096:ℝ) with hc | hc
      · rcases le_total y (8159/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8549/8192:ℝ) with hc | hc
            · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (138011869/10000000000000:ℝ) ≤ wfun (x + y) := wc_514 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (335458679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1101 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (30150607/2000000000000:ℝ) ≤ wfun (x + y) := wc_520 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1115 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_515 (x + y) (by linarith) (by linarith)
            have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
            have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
            have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
            have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1121 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
            have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
            have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8159/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8559/8192:ℝ) with hc | hc
            · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (82024953/5000000000000:ℝ) ≤ wfun (x + y) := wc_522 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (43501511/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1120 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
              have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
              have hw3 : (35580319/2000000000000:ℝ) ≤ wfun (x + y) := wc_526 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_529 (y + z) (by linarith) (by linarith)
              have hw5 : (1771842379/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1126 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_225 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_523 (x + y) (by linarith) (by linarith)
            have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
            have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_55 z (by linarith) (by linarith)
            have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
            have hw4 : (890387/40000000000:ℝ) ≤ wfun (y + z) := wc_539 (y + z) (by linarith) (by linarith)
            have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1130 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_227 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
            have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_529 (x + y) (by linarith) (by linarith)
            have hw4 : (255244651/10000000000000:ℝ) ≤ wfun (y + z) := wc_542 (y + z) (by linarith) (by linarith)
            have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1140 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_177 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (1023/512:ℝ))
    (hz1 : (539/512:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1073/1024:ℝ) with hc | hc
  · rcases le_total y (2041/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · rcases le_total y (4077/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · rcases le_total x (4277/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (5774823/625000000000:ℝ) ≤ wfun (x + y) := wc_480 (x + y) (by linarith) (by linarith)
                have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
                have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1147 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
                have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
                have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_507 (x + y) (by linarith) (by linarith)
                have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
                have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1160 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
              have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_481 (x + y) (by linarith) (by linarith)
              have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_560 (y + z) (by linarith) (by linarith)
              have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
            have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
            have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_561 (y + z) (by linarith) (by linarith)
            have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1165 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (4077/2048:ℝ) with hc | hc
          · rcases le_total z (2161/2048:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
              have hw2 : (6838799/2000000000000:ℝ) ≤ wfun z := wc_93 z (by linarith) (by linarith)
              have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
              have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_552 (y + z) (by linarith) (by linarith)
              have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1164 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
              have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_517 (x + y) (by linarith) (by linarith)
              have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_560 (y + z) (by linarith) (by linarith)
              have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1169 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
            have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_561 (y + z) (by linarith) (by linarith)
            have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1170 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
        have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
        have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
        have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
        have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1172 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2141/2048:ℝ) with hc | hc
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
          have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_532 (x + y) (by linarith) (by linarith)
          have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
          have hw5 : (2189105517/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1171 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
          have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_545 (x + y) (by linarith) (by linarith)
          have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
          have hw5 : (291380049/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1177 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
        have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
        have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
        have hw4 : (694482783/10000000000000:ℝ) ≤ wfun (y + z) := wc_570 (y + z) (by linarith) (by linarith)
        have hw5 : (3861047/15625000000:ℝ) ≤ wfun (x + y + z) := wc_1179 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total y (2041/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2151/2048:ℝ) with hc | hc
        · rcases le_total y (4077/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_217 y (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_531 (x + y) (by linarith) (by linarith)
            have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_553 (y + z) (by linarith) (by linarith)
            have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1170 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_226 y (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_544 (x + y) (by linarith) (by linarith)
            have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_561 (y + z) (by linarith) (by linarith)
            have hw5 : (2336612903/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1176 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
          have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
          have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_545 (x + y) (by linarith) (by linarith)
          have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_554 (y + z) (by linarith) (by linarith)
          have hw5 : (291380049/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1177 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
        have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
        have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
        have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_564 (y + z) (by linarith) (by linarith)
        have hw5 : (3861047/15625000000:ℝ) ≤ wfun (x + y + z) := wc_1179 (x + y + z) (by linarith) (by linarith)
        linarith
    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
      have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
      have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_565 (y + z) (by linarith) (by linarith)
      have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1180 (x + y + z) (by linarith) (by linarith)
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_188 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (257/128:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (509/256:ℝ) with hc | hc
  · rcases le_total z (519/256:ℝ) with hc | hc
    · rcases le_total x (529/512:ℝ) with hc | hc
      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
        have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
        have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
        linarith
      · rcases le_total y (1013/512:ℝ) with hc | hc
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
          have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
          have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (4:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_643 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_668 (y + z) (by linarith) (by linarith))
          linarith
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
          have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_165 y (by linarith) (by linarith)
          have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
          have hw5 : (3568011/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1220 (x + y + z) (by linarith) (by linarith)
          linarith
    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
      have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
      have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1222 (x + y + z) (by linarith) (by linarith)
      linarith
  · rcases le_total z (519/256:ℝ) with hc | hc
    · rcases le_total x (529/512:ℝ) with hc | hc
      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
        have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_244 z (by linarith) (by linarith)
        have hw5 : (14162149/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1221 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (1023/512:ℝ) with hc | hc
        · rcases le_total z (1033/512:ℝ) with hc | hc
          · rcases le_total x (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
              have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
              have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_364 (x + y) (by linarith) (by linarith)
              have hw5 : (19565737/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1239 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (2041/1024:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
                have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
                have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
                have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_673 (y + z) (by linarith) (by linarith))
                have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_1249 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (2061/1024:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                  have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
                  have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                  have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
                  have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_680 (y + z) (by linarith) (by linarith)
                  have hw5 : (38749297/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1262 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                  have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_246 z (by linarith) (by linarith)
                  have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
                  have hw5 : (134914401/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1288 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
              have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_364 (x + y) (by linarith) (by linarith)
              have hw5 : (19225319/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1265 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (2041/1024:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_218 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
                have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1290 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_230 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
                have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1312 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1033/512:ℝ) with hc | hc
          · rcases le_total x (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
              have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_243 z (by linarith) (by linarith)
              have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_484 (x + y) (by linarith) (by linarith)
              have hw5 : (19225319/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1265 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (2051/1024:ℝ) with hc | hc
              · rcases le_total z (2061/1024:ℝ) with hc | hc
                · rcases le_total x (2131/2048:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
                    have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                    have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_532 (x + y) (by linarith) (by linarith)
                    have hw5 : (67587843/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1286 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                    have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
                    have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                    have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_545 (x + y) (by linarith) (by linarith)
                    have hw5 : (12522987/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1301 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (2131/2048:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_246 z (by linarith) (by linarith)
                    have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_532 (x + y) (by linarith) (by linarith)
                    have hw5 : (71769027/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1308 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                    have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
                    have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_246 z (by linarith) (by linarith)
                    have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_545 (x + y) (by linarith) (by linarith)
                    have hw5 : (407642947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1327 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (2061/1024:ℝ) with hc | hc
                · rcases le_total x (2131/2048:ℝ) with hc | hc
                  · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_24 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
                    have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                    have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_553 (x + y) (by linarith) (by linarith)
                    have hw5 : (71769027/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1308 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
                    have hw2 : (543159341/10000000000000:ℝ) ≤ wfun z := wc_242 z (by linarith) (by linarith)
                    have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_561 (x + y) (by linarith) (by linarith)
                    have hw5 : (407642947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1327 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
                  have hw2 : (27945219/1000000000000:ℝ) ≤ wfun z := wc_246 z (by linarith) (by linarith)
                  have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
                  have hw4 : (64801/10000000000000:ℝ) ≤ wfun (y + z) := wc_698 (y + z) (by linarith) (by linarith)
                  have hw5 : (458561277/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1338 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
              have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
              have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_484 (x + y) (by linarith) (by linarith)
              have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_700 (y + z) (by linarith) (by linarith)
              have hw5 : (71079411/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1313 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (2051/1024:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_235 y (by linarith) (by linarith))
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_533 (x + y) (by linarith) (by linarith)
                have hw4 : (32243/5000000000000:ℝ) ≤ wfun (y + z) := wc_699 (y + z) (by linarith) (by linarith)
                have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1340 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_239 y (by linarith) (by linarith)
                have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_248 z (by linarith) (by linarith)
                have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_554 (x + y) (by linarith) (by linarith)
                have hw4 : (11791793/10000000000000:ℝ) ≤ wfun (y + z) := wc_734 (y + z) (by linarith) (by linarith)
                have hw5 : (568693187/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1367 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (529/512:ℝ) with hc | hc
      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
        have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_702 (y + z) (by linarith) (by linarith)
        have hw5 : (37716487/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1268 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (1023/512:ℝ) with hc | hc
        · rcases le_total z (1043/512:ℝ) with hc | hc
          · rcases le_total x (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
              have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_364 (x + y) (by linarith) (by linarith)
              have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_700 (y + z) (by linarith) (by linarith)
              have hw5 : (71079411/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1313 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
              have hw3 : (28290747/10000000000000:ℝ) ≤ wfun (x + y) := wc_422 (x + y) (by linarith) (by linarith)
              have hw4 : (32087/5000000000000:ℝ) ≤ wfun (y + z) := wc_700 (y + z) (by linarith) (by linarith)
              have hw5 : (91007427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1341 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_219 y (by linarith) (by linarith)
            have hw2 : (21355581/2500000000000:ℝ) ≤ wfun z := wc_250 z (by linarith) (by linarith)
            have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
            have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_757 (y + z) (by linarith) (by linarith)
            have hw5 : (112866211/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1369 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1043/512:ℝ) with hc | hc
          · rcases le_total x (1063/1024:ℝ) with hc | hc
            · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_18 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
              have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_484 (x + y) (by linarith) (by linarith)
              have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_757 (y + z) (by linarith) (by linarith)
              have hw5 : (566506871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1368 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
              have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_534 (x + y) (by linarith) (by linarith)
              have hw4 : (43419407/10000000000000:ℝ) ≤ wfun (y + z) := wc_757 (y + z) (by linarith) (by linarith)
              have hw5 : (68963139/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1401 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_233 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_236 y (by linarith) (by linarith))
            have hw2 : (21355581/2500000000000:ℝ) ≤ wfun z := wc_250 z (by linarith) (by linarith)
            have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
            have hw4 : (8305511/500000000000:ℝ) ≤ wfun (y + z) := wc_781 (y + z) (by linarith) (by linarith)
            have hw5 : (821066057/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1433 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_197 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (179/64:ℝ) ≤ y) (hy2 : y ≤ (747/256:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  have hw1 : (1457053011/2000000000000:ℝ) ≤ wfun y := wc_287 y (by linarith) (by linarith)
  linarith

set_option maxHeartbeats 20000000 in
lemma ch_203 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (3019/1024:ℝ) ≤ y) (hy2 : y ≤ (6069/2048:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2330/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (539/512:ℝ) with hc | hc
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total y (12107/4096:ℝ) with hc | hc
      · rcases le_total x (1073/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (29065073/5000000000000:ℝ) ≤ wfun (x + y) := by
              rcases le_total (x + y) (4:ℝ) with hq30 | hq30
              · exact le_trans (by norm_num) (wc_653 (x + y) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_666 (x + y) (by linarith) (by linarith))
            have hw4 : (29065073/5000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_653 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_666 (y + z) (by linarith) (by linarith))
            have hw5 : (129772853/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1248 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw3 : (29065073/5000000000000:ℝ) ≤ wfun (x + y) := by
              rcases le_total (x + y) (4:ℝ) with hq30 | hq30
              · exact le_trans (by norm_num) (wc_653 (x + y) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_666 (x + y) (by linarith) (by linarith))
            have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_671 (y + z) (by linarith) (by linarith))
            have hw5 : (48333597/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1263 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
            have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (9692591/5000000000000:ℝ) ≤ wfun (x + y) := by
              rcases le_total (x + y) (4:ℝ) with hq30 | hq30
              · exact le_trans (by norm_num) (wc_656 (x + y) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_671 (x + y) (by linarith) (by linarith))
            have hw4 : (29065073/5000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_653 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_666 (y + z) (by linarith) (by linarith))
            have hw5 : (48333597/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1263 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (24183/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (3697248069/10000000000000:ℝ) ≤ wfun y := wc_296 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
              have hw3 : (2379757/500000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_656 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_667 (x + y) (by linarith) (by linarith))
              have hw4 : (2379757/500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_667 (y + z) (by linarith) (by linarith))
              have hw5 : (135031901/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1287 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (3295569861/10000000000000:ℝ) ≤ wfun y := wc_300 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
              have hw3 : (9692591/5000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_660 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_671 (x + y) (by linarith) (by linarith))
              have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_660 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_671 (y + z) (by linarith) (by linarith))
              have hw5 : (337513471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1306 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (1073/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total y (24245/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_303 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (6571821/2500000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_659 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_670 (x + y) (by linarith) (by linarith))
              have hw4 : (6571821/2500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_659 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_670 (y + z) (by linarith) (by linarith))
              have hw5 : (9370879/400000000000:ℝ) ≤ wfun (x + y + z) := wc_1279 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (6937709/10000000000000:ℝ) ≤ wfun (x + y) := wc_684 (x + y) (by linarith) (by linarith)
              have hw4 : (6937709/10000000000000:ℝ) ≤ wfun (y + z) := wc_684 (y + z) (by linarith) (by linarith)
              have hw5 : (37182159/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1298 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (24245/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_303 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
              have hw3 : (6571821/2500000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_659 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_670 (x + y) (by linarith) (by linarith))
              have hw4 : (730337/2000000000000:ℝ) ≤ wfun (y + z) := wc_688 (y + z) (by linarith) (by linarith)
              have hw5 : (317177363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1302 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2141/2048:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (17994249/10000000000000:ℝ) ≤ wfun (x + y) := wc_683 (x + y) (by linarith) (by linarith)
                have hw5 : (390560199/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1324 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (6937709/10000000000000:ℝ) ≤ wfun (x + y) := wc_690 (x + y) (by linarith) (by linarith)
                have hw5 : (110339709/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1333 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total y (24245/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_303 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (730337/2000000000000:ℝ) ≤ wfun (x + y) := wc_688 (x + y) (by linarith) (by linarith)
              have hw4 : (6571821/2500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_659 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_670 (y + z) (by linarith) (by linarith))
              have hw5 : (317177363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1302 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (528153/5000000000000:ℝ) ≤ wfun (x + y) := wc_696 (x + y) (by linarith) (by linarith)
                have hw4 : (6937709/10000000000000:ℝ) ≤ wfun (y + z) := wc_684 (y + z) (by linarith) (by linarith)
                have hw5 : (390560199/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1324 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw4 : (6937709/10000000000000:ℝ) ≤ wfun (y + z) := wc_684 (y + z) (by linarith) (by linarith)
                have hw5 : (110339709/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1333 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (24245/8192:ℝ) with hc | hc
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_303 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (12377299/10000000000000:ℝ) ≤ wfun (x + y) := wc_687 (x + y) (by linarith) (by linarith)
                have hw4 : (730337/2000000000000:ℝ) ≤ wfun (y + z) := wc_688 (y + z) (by linarith) (by linarith)
                have hw5 : (82609501/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1328 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_303 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw3 : (730337/2000000000000:ℝ) ≤ wfun (x + y) := wc_693 (x + y) (by linarith) (by linarith)
                have hw4 : (730337/2000000000000:ℝ) ≤ wfun (y + z) := wc_688 (y + z) (by linarith) (by linarith)
                have hw5 : (465196871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1345 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                  have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw3 : (528153/5000000000000:ℝ) ≤ wfun (x + y) := wc_696 (x + y) (by linarith) (by linarith)
                  have hw4 : (528153/5000000000000:ℝ) ≤ wfun (y + z) := wc_696 (y + z) (by linarith) (by linarith)
                  have hw5 : (496110717/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1351 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                  have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw3 : (528153/5000000000000:ℝ) ≤ wfun (x + y) := wc_696 (x + y) (by linarith) (by linarith)
                  have hw5 : (110597717/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1362 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                  have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_71 z (by linarith) (by linarith)
                  have hw4 : (528153/5000000000000:ℝ) ≤ wfun (y + z) := wc_696 (y + z) (by linarith) (by linarith)
                  have hw5 : (110597717/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_1362 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                  have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_86 z (by linarith) (by linarith)
                  have hw5 : (306412007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1382 (x + y + z) (by linarith) (by linarith)
                  linarith
    · rcases le_total y (12107/4096:ℝ) with hc | hc
      · rcases le_total x (1073/1024:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
          have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
          have hw3 : (29065073/5000000000000:ℝ) ≤ wfun (x + y) := by
            rcases le_total (x + y) (4:ℝ) with hq30 | hq30
            · exact le_trans (by norm_num) (wc_653 (x + y) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_666 (x + y) (by linarith) (by linarith))
          have hw5 : (268216841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1291 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total y (24183/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (3697248069/10000000000000:ℝ) ≤ wfun y := wc_296 y (by linarith) (by linarith)
              have hw3 : (2379757/500000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_656 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_667 (x + y) (by linarith) (by linarith))
              have hw4 : (13534729/10000000000000:ℝ) ≤ wfun (y + z) := wc_679 (y + z) (by linarith) (by linarith)
              have hw5 : (89615951/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1309 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (3295569861/10000000000000:ℝ) ≤ wfun y := wc_300 y (by linarith) (by linarith)
              have hw3 : (9692591/5000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_660 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_671 (x + y) (by linarith) (by linarith))
              have hw4 : (70603/500000000000:ℝ) ≤ wfun (y + z) := wc_689 (y + z) (by linarith) (by linarith)
              have hw5 : (10882551/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1332 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
            have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw3 : (9692591/5000000000000:ℝ) ≤ wfun (x + y) := by
              rcases le_total (x + y) (4:ℝ) with hq30 | hq30
              · exact le_trans (by norm_num) (wc_656 (x + y) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_671 (x + y) (by linarith) (by linarith))
            have hw5 : (228794373/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1339 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (1073/1024:ℝ) with hc | hc
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total y (24245/8192:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_303 y (by linarith) (by linarith)
              have hw3 : (6571821/2500000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_659 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_670 (x + y) (by linarith) (by linarith))
              have hw5 : (51531267/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1329 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
              have hw3 : (6937709/10000000000000:ℝ) ≤ wfun (x + y) := wc_684 (x + y) (by linarith) (by linarith)
              have hw5 : (494198099/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1352 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw3 : (6937709/10000000000000:ℝ) ≤ wfun (x + y) := by
              rcases le_total (x + y) (4:ℝ) with hq30 | hq30
              · exact le_trans (by norm_num) (wc_659 (x + y) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_674 (x + y) (by linarith) (by linarith))
            have hw5 : (32361139/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1357 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total y (24245/8192:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
              have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_303 y (by linarith) (by linarith)
              have hw3 : (730337/2000000000000:ℝ) ≤ wfun (x + y) := wc_688 (x + y) (by linarith) (by linarith)
              have hw5 : (519328881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1356 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2151/2048:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_71 x (by linarith) (by linarith)
                have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                have hw3 : (528153/5000000000000:ℝ) ≤ wfun (x + y) := wc_696 (x + y) (by linarith) (by linarith)
                have hw5 : (152910611/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1383 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_86 x (by linarith) (by linarith)
                have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                have hw5 : (674292103/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1394 (x + y + z) (by linarith) (by linarith)
                linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_72 x (by linarith) (by linarith)
            have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw5 : (318168869/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1389 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total y (12107/4096:ℝ) with hc | hc
      · rcases le_total x (1083/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (70603/500000000000:ℝ) ≤ wfun (x + y) := wc_681 (x + y) (by linarith) (by linarith)
            have hw4 : (29065073/5000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_653 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_666 (y + z) (by linarith) (by linarith))
            have hw5 : (269255433/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1289 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (24183/8192:ℝ) with hc | hc
            · have hw1 : (3697248069/10000000000000:ℝ) ≤ wfun y := wc_296 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
              have hw3 : (13534729/10000000000000:ℝ) ≤ wfun (x + y) := wc_679 (x + y) (by linarith) (by linarith)
              have hw4 : (2379757/500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_667 (y + z) (by linarith) (by linarith))
              have hw5 : (89615951/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1309 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (3295569861/10000000000000:ℝ) ≤ wfun y := wc_300 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
              have hw3 : (70603/500000000000:ℝ) ≤ wfun (x + y) := wc_689 (x + y) (by linarith) (by linarith)
              have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_660 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_671 (y + z) (by linarith) (by linarith))
              have hw5 : (10882551/250000000000:ℝ) ≤ wfun (x + y + z) := wc_1332 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw4 : (29065073/5000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_653 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_666 (y + z) (by linarith) (by linarith))
            have hw5 : (89347967/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1311 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_656 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_671 (y + z) (by linarith) (by linarith))
            have hw5 : (228794373/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1339 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total x (1083/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total y (24245/8192:ℝ) with hc | hc
            · have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_303 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw4 : (6571821/2500000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_659 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_670 (y + z) (by linarith) (by linarith))
              have hw5 : (51531267/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1329 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw4 : (6937709/10000000000000:ℝ) ≤ wfun (y + z) := wc_684 (y + z) (by linarith) (by linarith)
              have hw5 : (494198099/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1352 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (24245/8192:ℝ) with hc | hc
            · have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_303 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
              have hw4 : (730337/2000000000000:ℝ) ≤ wfun (y + z) := wc_688 (y + z) (by linarith) (by linarith)
              have hw5 : (519328881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1356 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (2161/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_93 x (by linarith) (by linarith)
                have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw5 : (152910611/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_1383 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
                have hw5 : (674292103/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1394 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw4 : (6937709/10000000000000:ℝ) ≤ wfun (y + z) := by
              rcases le_total (y + z) (4:ℝ) with hq40 | hq40
              · exact le_trans (by norm_num) (wc_659 (y + z) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_674 (y + z) (by linarith) (by linarith))
            have hw5 : (32361139/625000000000:ℝ) ≤ wfun (x + y + z) := wc_1357 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
            have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_72 z (by linarith) (by linarith)
            have hw5 : (318168869/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1389 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (12107/4096:ℝ) with hc | hc
      · have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_297 y (by linarith) (by linarith)
        have hw5 : (227036969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_1342 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (1083/1024:ℝ) with hc | hc
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total y (24245/8192:ℝ) with hc | hc
            · have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_303 y (by linarith) (by linarith)
              have hw5 : (638241617/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1388 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_305 y (by linarith) (by linarith)
              have hw5 : (73842291/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_1415 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_98 z (by linarith) (by linarith)
            have hw5 : (766514859/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_1419 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_98 x (by linarith) (by linarith)
          have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_304 y (by linarith) (by linarith)
          have hw5 : (95446393/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_1420 (x + y + z) (by linarith) (by linarith)
          linarith

end Zeta23Ext.Bridge.FourPoint
