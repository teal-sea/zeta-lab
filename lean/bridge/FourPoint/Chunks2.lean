import FourPoint.Cells

/-! Chunk module 2 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_18 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (131/128:ℝ) ≤ z) (hz2 : z ≤ (529/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (1073/1024:ℝ) with hc | hc
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
      have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
      have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_224 (y + z) (by linarith) (by linarith)
      have hw5 : (183260287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_528 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total z (1053/1024:ℝ) with hc | hc
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
        have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
        have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
        have hw5 : (99536523/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_537 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_14 z (by linarith) (by linarith)
        have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
        have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_545 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total y (2031/1024:ℝ) with hc | hc
    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
      have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
      have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
      have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
      have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_224 (y + z) (by linarith) (by linarith)
      have hw5 : (495290917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_538 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total z (1053/1024:ℝ) with hc | hc
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
        have hw2 : (3436255003/5000000000000:ℝ) ≤ wfun z := wc_11 z (by linarith) (by linarith)
        have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
        have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_228 (y + z) (by linarith) (by linarith)
        have hw5 : (645862429/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_545 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
        have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
        have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_14 z (by linarith) (by linarith)
        have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
        have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_563 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_34 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (2151/2048:ℝ) with hc | hc
  · rcases le_total y (4057/2048:ℝ) with hc | hc
    · rcases le_total z (2141/2048:ℝ) with hc | hc
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_624 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_624 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
                have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
                have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16213/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_101 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                  have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_253 (y + z) (by linarith) (by linarith)
                  have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_106 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                  have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_259 (y + z) (by linarith) (by linarith)
                  have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16213/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_101 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                  have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                  have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_106 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                  have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16223/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                  have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                  have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                  have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16223/8192:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                  have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                  have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16223/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                  have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                  have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16223/8192:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                  have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                  have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total z (2141/2048:ℝ) with hc | hc
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16233/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                  have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                  have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                  have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                  have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16243/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                  have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_294 (x + y) (by linarith) (by linarith)
                  have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (4297/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16233/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                  have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                  have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                  have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16233/8192:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                  have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                  have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                  have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16233/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                  have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                  have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (16233/8192:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                  have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                  have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                  have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                  have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_669 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16243/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                  have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                  have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_294 (x + y) (by linarith) (by linarith)
                  have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                  have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8589/8192:ℝ) with hc | hc
              · rcases le_total y (16243/8192:ℝ) with hc | hc
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                  have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                  have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_669 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (3813691/62500000000:ℝ) ≤ wfun x := wc_42 x (by linarith) (by linarith)
                  have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_294 (x + y) (by linarith) (by linarith)
                  have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                  have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_677 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_46 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8599/8192:ℝ) with hc | hc
              · have hw0 : (225854567/5000000000000:ℝ) ≤ wfun x := wc_47 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_49 x (by linarith) (by linarith)
                have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total y (4057/2048:ℝ) with hc | hc
    · rcases le_total z (2141/2048:ℝ) with hc | hc
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8109/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (2141/2048:ℝ) with hc | hc
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4277/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4307/4096:ℝ) with hc | hc
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8119/4096:ℝ) with hc | hc
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4287/4096:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_46 (x y z : ℝ) (hx1 : (539/512:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                  have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                  have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                  have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                  have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
                have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_321 (y + z) (by linarith) (by linarith)
                have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_723 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
                have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_301 (y + z) (by linarith) (by linarith)
                have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_723 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
                have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_321 (y + z) (by linarith) (by linarith)
                have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_726 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4077/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                have hw4 : (7636599/400000000000:ℝ) ≤ wfun (y + z) := wc_327 (y + z) (by linarith) (by linarith)
                have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_726 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
                have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
                have hw5 : (2336612903/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_731 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
              have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
              have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
              have hw5 : (291380049/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_732 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
            have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
            have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
            have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
            have hw5 : (3861047/15625000000:ℝ) ≤ wfun (x + y + z) := wc_733 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
            have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
            have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
            have hw5 : (3861047/15625000000:ℝ) ≤ wfun (x + y + z) := wc_733 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
          have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
          have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_734 (x + y + z) (by linarith) (by linarith)
          linarith
    · have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
      have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
      have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_736 (x + y + z) (by linarith) (by linarith)
      linarith
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2051/1024:ℝ) with hc | hc
        · have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
          have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
          have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
          have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_734 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
          have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
          have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
          have hw5 : (690206739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_743 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
        have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
        have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
        have hw5 : (549546581/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_744 (x + y + z) (by linarith) (by linarith)
        linarith
    · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
        rcases le_total y (2:ℝ) with hq10 | hq10
        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
      have hw5 : (3048526697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_746 (x + y + z) (by linarith) (by linarith)
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_54 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (63/32:ℝ) ≤ z) (hz2 : z ≤ (257/128:ℝ)) :
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
      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
        rcases le_total z (2:ℝ) with hq20 | hq20
        · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
      have hw4 : (38435113/2500000000000:ℝ) ≤ wfun (y + z) := wc_406 (y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total z (509/256:ℝ) with hc | hc
      · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
        have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
        have hw4 : (31317919/2000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (529/512:ℝ) with hc | hc
        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
          have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
            rcases le_total z (2:ℝ) with hq20 | hq20
            · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
          linarith
        · rcases le_total y (1023/512:ℝ) with hc | hc
          · rcases le_total z (1023/512:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
              have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
              have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
              have hw4 : (39629583/2500000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (1063/1024:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_245 (x + y) (by linarith) (by linarith)
                have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                have hw5 : (2887779/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_767 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (28290747/10000000000000:ℝ) ≤ wfun (x + y) := wc_273 (x + y) (by linarith) (by linarith)
                have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                have hw5 : (5002981/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_777 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (1023/512:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
              have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
              have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
              have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
              have hw5 : (449469/312500000000:ℝ) ≤ wfun (x + y + z) := wc_768 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (1063/1024:ℝ) with hc | hc
              · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_303 (x + y) (by linarith) (by linarith)
                have hw5 : (19565737/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_786 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                  have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
                  have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                  have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                  linarith
  · rcases le_total y (509/256:ℝ) with hc | hc
    · rcases le_total z (509/256:ℝ) with hc | hc
      · have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
        have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
        have hw4 : (319416431/5000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total x (539/512:ℝ) with hc | hc
        · rcases le_total y (1013/512:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
            have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
              rcases le_total z (2:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
            have hw4 : (71867913/2000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (1023/512:ℝ) with hc | hc
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
              have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
              have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
              have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
              have hw4 : (11299473/312500000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_245 (x + y) (by linarith) (by linarith)
                have hw4 : (39629583/2500000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                have hw5 : (2887779/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_767 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (28290747/10000000000000:ℝ) ≤ wfun (x + y) := wc_273 (x + y) (by linarith) (by linarith)
                have hw4 : (39629583/2500000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                have hw5 : (5002981/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_777 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (1013/512:ℝ) with hc | hc
          · have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
            have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
              rcases le_total z (2:ℝ) with hq20 | hq20
              · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
            have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
            have hw4 : (71867913/2000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (1023/512:ℝ) with hc | hc
            · have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
              have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
              have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
              have hw4 : (11299473/312500000000:ℝ) ≤ wfun (y + z) := wc_413 (y + z) (by linarith) (by linarith)
              have hw5 : (449469/312500000000:ℝ) ≤ wfun (x + y + z) := wc_768 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
              have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
              have hw4 : (39629583/2500000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
              have hw5 : (38980307/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_787 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total z (509/256:ℝ) with hc | hc
      · rcases le_total x (539/512:ℝ) with hc | hc
        · rcases le_total y (1023/512:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
            have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
            have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
            have hw4 : (71867913/2000000000000:ℝ) ≤ wfun (y + z) := wc_409 (y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
            have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
            have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
            have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
            have hw4 : (157670757/10000000000000:ℝ) ≤ wfun (y + z) := wc_414 (y + z) (by linarith) (by linarith)
            linarith
        · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
          have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
          have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
          have hw4 : (31317919/2000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total x (539/512:ℝ) with hc | hc
        · rcases le_total y (1023/512:ℝ) with hc | hc
          · rcases le_total z (1023/512:ℝ) with hc | hc
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                have hw3 : (91064031/10000000000000:ℝ) ≤ wfun (x + y) := wc_303 (x + y) (by linarith) (by linarith)
                have hw4 : (39629583/2500000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                have hw5 : (2887779/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_767 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                have hw3 : (189078223/10000000000000:ℝ) ≤ wfun (x + y) := wc_329 (x + y) (by linarith) (by linarith)
                have hw4 : (39629583/2500000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
                have hw5 : (5002981/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_777 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
                  have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                  have hw5 : (314267/40000000000:ℝ) ≤ wfun (x + y + z) := wc_785 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (2051/1024:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                    have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 z (by linarith) (by linarith))
                    have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                    have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                    have hw5 : (16256217/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_793 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (2141/2048:ℝ) with hc | hc
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                      have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_327 (x + y) (by linarith) (by linarith)
                      have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                      have hw5 : (194122073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_802 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                      have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
                      have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                      have hw5 : (115347177/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_819 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · rcases le_total z (2051/1024:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                    have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 z (by linarith) (by linarith))
                    have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                    have hw4 : (39782441/2500000000000:ℝ) ≤ wfun (y + z) := wc_424 (y + z) (by linarith) (by linarith)
                    have hw5 : (16256217/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_793 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                    have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
                    have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                    have hw5 : (38749297/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_803 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (2051/1024:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                    have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 z (by linarith) (by linarith))
                    have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                    have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                    have hw5 : (38749297/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_803 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (2151/2048:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                      have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_341 (x + y) (by linarith) (by linarith)
                      have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                      have hw5 : (67587843/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_825 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                      have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                      have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                      have hw5 : (12522987/400000000000:ℝ) ≤ wfun (x + y + z) := wc_835 (x + y + z) (by linarith) (by linarith)
                      linarith
          · rcases le_total z (1023/512:ℝ) with hc | hc
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                  have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                  have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                  have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                  have hw5 : (314267/40000000000:ℝ) ≤ wfun (x + y + z) := wc_785 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                  have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                  have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                  have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                  have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                  have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                  have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                  have hw5 : (6477343/500000000000:ℝ) ≤ wfun (x + y + z) := wc_794 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
                  have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                  have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                  have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (1073/1024:ℝ) with hc | hc
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · rcases le_total z (2051/1024:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                    have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 z (by linarith) (by linarith))
                    have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                    have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                    have hw5 : (38749297/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_803 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (2141/2048:ℝ) with hc | hc
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                      have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_341 (x + y) (by linarith) (by linarith)
                      have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                      have hw5 : (67587843/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_825 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                      have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
                      have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                      have hw5 : (12522987/400000000000:ℝ) ≤ wfun (x + y + z) := wc_835 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (2051/1024:ℝ) with hc | hc
                  · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                    have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 z (by linarith) (by linarith))
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                    have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                    have hw5 : (134914401/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_826 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (2141/2048:ℝ) with hc | hc
                    · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                      have hw3 : (493784853/10000000000000:ℝ) ≤ wfun (x + y) := wc_349 (x + y) (by linarith) (by linarith)
                      have hw5 : (71769027/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
                      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                      have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                      have hw5 : (407642947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_853 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · rcases le_total z (2051/1024:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                    have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 z (by linarith) (by linarith))
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                    have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                    have hw5 : (134914401/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_826 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · rcases le_total x (2151/2048:ℝ) with hc | hc
                    · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                      have hw3 : (493784853/10000000000000:ℝ) ≤ wfun (x + y) := wc_349 (x + y) (by linarith) (by linarith)
                      have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                      have hw5 : (71769027/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_839 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
                      have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                      have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
                      have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                      have hw5 : (407642947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_853 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total z (2051/1024:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                    have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 z (by linarith) (by linarith))
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                    have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := wc_444 (y + z) (by linarith) (by linarith)
                    have hw5 : (358152183/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                    have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                    have hw5 : (458561277/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_859 (x + y + z) (by linarith) (by linarith)
                    linarith
        · rcases le_total y (1023/512:ℝ) with hc | hc
          · rcases le_total z (1023/512:ℝ) with hc | hc
            · have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
              have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
              have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
              have hw4 : (39629583/2500000000000:ℝ) ≤ wfun (y + z) := wc_418 (y + z) (by linarith) (by linarith)
              have hw5 : (38980307/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_787 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (1083/1024:ℝ) with hc | hc
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
                  have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                  have hw5 : (12062377/625000000000:ℝ) ≤ wfun (x + y + z) := wc_805 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total z (2051/1024:ℝ) with hc | hc
                  · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                    have hw2 : (1337086167/10000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_140 z (by linarith) (by linarith))
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                    have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                    have hw5 : (134914401/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_826 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := wc_143 z (by linarith) (by linarith)
                    have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                    have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                    have hw5 : (358152183/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_840 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (2041/1024:ℝ) with hc | hc
                · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                  have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
                  have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                  have hw5 : (53757489/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_828 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                  have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                  have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                  have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total z (1023/512:ℝ) with hc | hc
            · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
              have hw2 : (1865845891/10000000000000:ℝ) ≤ wfun z := wc_129 z (by linarith) (by linarith)
              have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
              have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_425 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
              have hw5 : (191511939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_807 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (1083/1024:ℝ) with hc | hc
              · rcases le_total y (2051/1024:ℝ) with hc | hc
                · have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
                  have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
                  have hw5 : (356771293/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_842 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (930293373/10000000000000:ℝ) ≤ wfun (x + y) := wc_362 (x + y) (by linarith) (by linarith)
                  have hw5 : (114198739/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_860 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_138 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (924357731/10000000000000:ℝ) ≤ wfun (x + y) := wc_363 (x + y) (by linarith) (by linarith)
                have hw5 : (91007427/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_861 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_64 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (747/256:ℝ) ≤ y) (hy2 : y ≤ (389/128:ℝ))
    (hz1 : (17/16:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (1525/512:ℝ) with hc | hc
  · rcases le_total x (131/128:ℝ) with hc | hc
    · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
        rcases le_total x (1:ℝ) with hq00 | hq00
        · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
      have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
      have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
      have hw3 : (76620491/10000000000000:ℝ) ≤ wfun (x + y) := by
        rcases le_total (x + y) (4:ℝ) with hq30 | hq30
        · exact le_trans (by norm_num) (wc_404 (x + y) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_433 (x + y) (by linarith) (by linarith))
      linarith
    · rcases le_total z (141/128:ℝ) with hc | hc
      · rcases le_total y (3019/1024:ℝ) with hc | hc
        · rcases le_total x (267/256:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
            have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
            have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (122092393/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
            linarith
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total y (6007/2048:ℝ) with hc | hc
              · have hw1 : (2995265257/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (82600037/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
                have hw4 : (4221/10000000000000:ℝ) ≤ wfun (y + z) := by
                  rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                  · exact le_trans (by norm_num) (wc_420 (y + z) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_443 (y + z) (by linarith) (by linarith))
                have hw5 : (33101423/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_774 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (816631931/2000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (436723/500000000000:ℝ) ≤ wfun (x + y) := by
                  rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                  · exact le_trans (by norm_num) (wc_417 (x + y) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_439 (x + y) (by linarith) (by linarith))
                have hw5 : (181069953/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_801 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (436723/500000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_412 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_439 (x + y) (by linarith) (by linarith))
              have hw5 : (242928173/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_821 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (267/256:ℝ) with hc | hc
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total y (6069/2048:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
                have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (34242453/10000000000000:ℝ) ≤ wfun (x + y) := by
                  rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                  · exact le_trans (by norm_num) (wc_416 (x + y) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_436 (x + y) (by linarith) (by linarith))
                have hw5 : (31511369/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_797 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total x (529/512:ℝ) with hc | hc
                · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                  have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw3 : (2673983/5000000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_426 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_441 (x + y) (by linarith) (by linarith))
                  have hw4 : (11743211/2500000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                  have hw5 : (14364449/400000000000:ℝ) ≤ wfun (x + y + z) := wc_851 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                  have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw4 : (11743211/2500000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                  have hw5 : (569259631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_890 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (67339097/500000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw4 : (92147329/10000000000000:ℝ) ≤ wfun (y + z) := wc_501 (y + z) (by linarith) (by linarith)
              have hw5 : (439255509/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_863 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total y (6069/2048:ℝ) with hc | hc
              · rcases le_total x (539/512:ℝ) with hc | hc
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total y (12107/4096:ℝ) with hc | hc
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                      have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                      have hw3 : (9692591/5000000000000:ℝ) ≤ wfun (x + y) := by
                        rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                        · exact le_trans (by norm_num) (wc_428 (x + y) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_437 (x + y) (by linarith) (by linarith))
                      have hw5 : (227036969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_862 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                      have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                      have hw4 : (2002543/5000000000000:ℝ) ≤ wfun (y + z) := wc_469 (y + z) (by linarith) (by linarith)
                      have hw5 : (63145721/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                    have hw4 : (11672323/10000000000000:ℝ) ≤ wfun (y + z) := wc_477 (y + z) (by linarith) (by linarith)
                    have hw5 : (342044549/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_904 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw5 : (339431207/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_905 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total x (539/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw4 : (11743211/2500000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                  have hw5 : (165046307/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_928 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw3 : (32421/1000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
                  have hw4 : (11743211/2500000000000:ℝ) ≤ wfun (y + z) := wc_495 (y + z) (by linarith) (by linarith)
                  have hw5 : (1125526841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_953 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw1 : (67339097/500000000000:ℝ) ≤ wfun y := wc_196 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw4 : (92147329/10000000000000:ℝ) ≤ wfun (y + z) := wc_501 (y + z) (by linarith) (by linarith)
              have hw5 : (936576257/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_937 (x + y + z) (by linarith) (by linarith)
              linarith
      · have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
        have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
        have hw4 : (1440757/2000000000000:ℝ) ≤ wfun (y + z) := wc_473 (y + z) (by linarith) (by linarith)
        have hw5 : (46032101/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_823 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total x (131/128:ℝ) with hc | hc
    · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
        rcases le_total x (1:ℝ) with hq00 | hq00
        · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
      have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
      have hw4 : (246785359/10000000000000:ℝ) ≤ wfun (y + z) := wc_525 (y + z) (by linarith) (by linarith)
      have hw5 : (41391449/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_783 (x + y + z) (by linarith) (by linarith)
      linarith
    · rcases le_total z (141/128:ℝ) with hc | hc
      · rcases le_total y (3081/1024:ℝ) with hc | hc
        · rcases le_total x (267/256:ℝ) with hc | hc
          · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
            have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (3:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_212 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
            have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw4 : (263915387/10000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (340218131/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_911 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw1 : (102076243/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (3:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_212 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_220 y (by linarith) (by linarith))
            have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
            have hw3 : (999363/625000000000:ℝ) ≤ wfun (x + y) := wc_483 (x + y) (by linarith) (by linarith)
            have hw4 : (263915387/10000000000000:ℝ) ≤ wfun (y + z) := wc_523 (y + z) (by linarith) (by linarith)
            have hw5 : (252901217/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_960 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
          have hw3 : (7204521/625000000000:ℝ) ≤ wfun (x + y) := wc_505 (x + y) (by linarith) (by linarith)
          have hw4 : (1219525351/10000000000000:ℝ) ≤ wfun (y + z) := wc_625 (y + z) (by linarith) (by linarith)
          have hw5 : (815292227/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_965 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
        have hw4 : (1572805651/10000000000000:ℝ) ≤ wfun (y + z) := wc_695 (y + z) (by linarith) (by linarith)
        have hw5 : (1934302493/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_966 (x + y + z) (by linarith) (by linarith)
        linarith

end Zeta23Ext.Bridge.FourPoint
