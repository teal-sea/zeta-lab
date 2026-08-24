import FourPoint.Cells

/-! Chunk module 5 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_3 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (63/64:ℝ) ≤ y) (hy2 : y ≤ (73/64:ℝ))
    (hz1 : (237/64:ℝ) ≤ z) (hz2 : z ≤ (231/40:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (3033/640:ℝ) with hc | hc
  · rcases le_total z (5403/1280:ℝ) with hc | hc
    · rcases le_total z (10143/2560:ℝ) with hc | hc
      · have hw2 : (957611737/10000000000000:ℝ) ≤ wfun z := by
          rcases le_total z (15/4:ℝ) with hq20 | hq20
          · exact le_trans (by norm_num) (wc_402 z (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_403 z (by linarith) (by linarith))
        linarith
      · linarith
    · linarith
  · linarith

set_option maxHeartbeats 20000000 in
lemma ch_15 (x y z : ℝ) (hx1 : (131/128:ℝ) ≤ x) (hx2 : x ≤ (529/512:ℝ))
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
    · rcases le_total x (1053/1024:ℝ) with hc | hc
      · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
        have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
        have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
        have hw5 : (79960111/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_547 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (2041/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
            have hw5 : (812553443/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_563 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
            have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
            have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_584 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
            have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
            have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
            have hw5 : (249365309/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_584 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
            have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
            have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
            have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_613 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (1053/1024:ℝ) with hc | hc
      · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
        have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
        have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
        have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_586 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
        have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
        have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
        have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_615 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total x (1053/1024:ℝ) with hc | hc
      · have hw0 : (3436255003/5000000000000:ℝ) ≤ wfun x := wc_11 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
        have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_245 (x + y) (by linarith) (by linarith)
        have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
        have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_586 (x + y + z) (by linarith) (by linarith)
        linarith
      · rcases le_total y (2051/1024:ℝ) with hc | hc
        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
          have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
          have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
          have hw4 : (160947823/5000000000000:ℝ) ≤ wfun (y + z) := wc_343 (y + z) (by linarith) (by linarith)
          have hw5 : (37329233/312500000000:ℝ) ≤ wfun (x + y + z) := wc_614 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_14 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
          have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
          have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
          have hw5 : (1413886087/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_652 (x + y + z) (by linarith) (by linarith)
          linarith
    · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
        rcases le_total y (2:ℝ) with hq10 | hq10
        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
      have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
      have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_654 (x + y + z) (by linarith) (by linarith)
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_29 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (1013/512:ℝ) ≤ y) (hy2 : y ≤ (2031/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (4057/2048:ℝ) with hc | hc
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
            have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_601 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_605 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (36283957/312500000000:ℝ) ≤ wfun (x + y + z) := wc_601 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (118742829/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_605 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_617 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
            have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
            have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (1846343/1000000000000:ℝ) ≤ wfun (x + y) := wc_261 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (23335779/10000000000000:ℝ) ≤ wfun (x + y) := wc_265 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_617 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_617 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_253 (y + z) (by linarith) (by linarith)
                have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_618 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_259 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_623 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_253 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_623 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_259 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_101 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_258 (x + y) (by linarith) (by linarith)
                have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_253 (y + z) (by linarith) (by linarith)
                have hw5 : (155211591/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_616 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_106 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_260 (x + y) (by linarith) (by linarith)
                have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_259 (y + z) (by linarith) (by linarith)
                have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_618 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_101 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (221417/156250000000:ℝ) ≤ wfun (x + y) := wc_258 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_623 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_106 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_260 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_260 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_618 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_623 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_623 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_260 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (8109/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_101 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_260 (x + y) (by linarith) (by linarith)
                have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_253 (y + z) (by linarith) (by linarith)
                have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_618 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_106 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_259 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_623 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_101 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                have hw4 : (5211923/5000000000000:ℝ) ≤ wfun (y + z) := wc_253 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_623 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_106 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                have hw4 : (3539799/2500000000000:ℝ) ≤ wfun (y + z) := wc_259 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_101 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (4619603/2500000000000:ℝ) ≤ wfun (x + y) := wc_260 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_106 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16213/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (1199722203/2500000000000:ℝ) ≤ wfun y := wc_101 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (23354711/10000000000000:ℝ) ≤ wfun (x + y) := wc_264 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4682565917/10000000000000:ℝ) ≤ wfun y := wc_106 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16223/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4567709043/10000000000000:ℝ) ≤ wfun y := wc_107 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (44543171/100000000000:ℝ) ≤ wfun y := wc_109 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_617 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                have hw5 : (634442007/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_618 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_623 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                have hw5 : (648175967/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_623 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_624 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_624 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (1846343/1000000000000:ℝ) ≤ wfun (y + z) := wc_261 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (23335779/10000000000000:ℝ) ≤ wfun (y + z) := wc_265 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (1324095821/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_626 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (338028751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_634 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (28798809/10000000000000:ℝ) ≤ wfun (x + y) := wc_266 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (17404961/5000000000000:ℝ) ≤ wfun (x + y) := wc_274 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (8119/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (28775469/10000000000000:ℝ) ≤ wfun (y + z) := wc_267 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (6956343/2000000000000:ℝ) ≤ wfun (y + z) := wc_275 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (20693629/5000000000000:ℝ) ≤ wfun (x + y) := wc_276 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16233/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (2171194499/5000000000000:ℝ) ≤ wfun y := wc_110 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (2426501/500000000000:ℝ) ≤ wfun (x + y) := wc_280 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4231923619/10000000000000:ℝ) ≤ wfun y := wc_113 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16243/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (4122919829/10000000000000:ℝ) ≤ wfun y := wc_114 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (2007688237/5000000000000:ℝ) ≤ wfun y := wc_116 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_669 (x + y + z) (by linarith) (by linarith)
                linarith

set_option maxHeartbeats 20000000 in
lemma ch_33 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (2141/2048:ℝ) with hc | hc
  · rcases le_total y (4067/2048:ℝ) with hc | hc
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8549/8192:ℝ) with hc | hc
              · have hw0 : (1488952289/10000000000000:ℝ) ≤ wfun x := wc_26 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (28775469/10000000000000:ℝ) ≤ wfun (x + y) := wc_267 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_31 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (6956343/2000000000000:ℝ) ≤ wfun (x + y) := wc_275 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (4135373/1000000000000:ℝ) ≤ wfun (x + y) := wc_277 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (48490713/10000000000000:ℝ) ≤ wfun (x + y) := wc_281 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
            have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
            have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
            have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
            have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
            have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
            have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
            have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
            have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_324 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_324 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
            have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
            have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
            have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
            have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
            have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
            have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
            have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
            have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total y (4067/2048:ℝ) with hc | hc
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (335458679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_684 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_694 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
            have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
            have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8129/4096:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
            have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
            have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
            have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
            have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_324 (y + z) (by linarith) (by linarith)
              have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
              have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
              have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
              have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
              have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
              have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_324 (y + z) (by linarith) (by linarith)
              have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_705 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
            have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
            have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
            have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
            have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8139/4096:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
            have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
            have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
            have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
            have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_708 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_48 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (17/16:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (131/128:ℝ) with hc | hc
  · rcases le_total y (257/128:ℝ) with hc | hc
    · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
        rcases le_total x (1:ℝ) with hq00 | hq00
        · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
        rcases le_total y (2:ℝ) with hq10 | hq10
        · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
      have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
      have hw4 : (79711817/10000000000000:ℝ) ≤ wfun (y + z) := wc_310 (y + z) (by linarith) (by linarith)
      have hw5 : (56143/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_459 (x + y + z) (by linarith) (by linarith)
      linarith
    · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
        rcases le_total x (1:ℝ) with hq00 | hq00
        · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
      have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
      have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
      have hw5 : (563044583/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_555 (x + y + z) (by linarith) (by linarith)
      linarith
  · rcases le_total y (257/128:ℝ) with hc | hc
    · rcases le_total z (141/128:ℝ) with hc | hc
      · rcases le_total x (267/256:ℝ) with hc | hc
        · rcases le_total y (509/256:ℝ) with hc | hc
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total x (529/512:ℝ) with hc | hc
              · rcases le_total y (1013/512:ℝ) with hc | hc
                · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                  have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw3 : (28217469/5000000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (3:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_215 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_221 (x + y) (by linarith) (by linarith))
                  have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_305 (y + z) (by linarith) (by linarith)
                  have hw5 : (315273331/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_549 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                  have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                  have hw5 : (973863897/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_588 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total y (1013/512:ℝ) with hc | hc
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total x (1063/1024:ℝ) with hc | hc
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                      have hw3 : (128333/125000000000:ℝ) ≤ wfun (x + y) := wc_224 (x + y) (by linarith) (by linarith)
                      have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                      have hw5 : (197587481/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_586 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                      have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                      have hw5 : (74301831/625000000000:ℝ) ≤ wfun (x + y + z) := wc_615 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                    have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                    have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                    have hw5 : (140043451/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_654 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total x (1063/1024:ℝ) with hc | hc
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                      have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                      have hw5 : (703570097/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_653 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                      have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                      have hw5 : (1642534177/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_693 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                    have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                    have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                    have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_716 (x + y + z) (by linarith) (by linarith)
                    linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (1361028853/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_657 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                have hw5 : (274801629/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_656 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total y (1023/512:ℝ) with hc | hc
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                  have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                  have hw4 : (676941261/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                  have hw5 : (933899467/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_717 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                  have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                  have hw5 : (2413024171/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_737 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_370 (y + z) (by linarith) (by linarith)
              have hw5 : (591952751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_738 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (509/256:ℝ) with hc | hc
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total y (1013/512:ℝ) with hc | hc
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · rcases le_total y (2021/1024:ℝ) with hc | hc
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                        have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                        have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_303 (y + z) (by linarith) (by linarith)
                        have hw5 : (1413886087/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_652 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                        have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
                        have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                        have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
                        have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_692 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                      have hw4 : (18095851/2000000000000:ℝ) ≤ wfun (y + z) := wc_304 (y + z) (by linarith) (by linarith)
                      have hw5 : (1642534177/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_693 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                    have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                    have hw5 : (942826837/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_716 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total z (549/512:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                      have hw3 : (1166349/10000000000000:ℝ) ≤ wfun (x + y) := wc_245 (x + y) (by linarith) (by linarith)
                      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                      have hw5 : (947330549/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_715 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                      have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                      have hw2 : (9984781/500000000000:ℝ) ≤ wfun z := wc_60 z (by linarith) (by linarith)
                      have hw3 : (28290747/10000000000000:ℝ) ≤ wfun (x + y) := wc_273 (x + y) (by linarith) (by linarith)
                      have hw4 : (63967043/2000000000000:ℝ) ≤ wfun (y + z) := wc_344 (y + z) (by linarith) (by linarith)
                      have hw5 : (216315697/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_730 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                    have hw2 : (1609622259/10000000000000:ℝ) ≤ wfun z := wc_65 z (by linarith) (by linarith)
                    have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                    have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
                    have hw5 : (1218017847/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_736 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total y (1013/512:ℝ) with hc | hc
                · have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw3 : (231767/2000000000000:ℝ) ≤ wfun (x + y) := wc_246 (x + y) (by linarith) (by linarith)
                  have hw4 : (22330933/2500000000000:ℝ) ≤ wfun (y + z) := wc_305 (y + z) (by linarith) (by linarith)
                  have hw5 : (933899467/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_717 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                  have hw4 : (157881813/5000000000000:ℝ) ≤ wfun (y + z) := wc_345 (y + z) (by linarith) (by linarith)
                  have hw5 : (2413024171/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_737 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
              have hw5 : (591952751/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_738 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (277/256:ℝ) with hc | hc
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total y (1023/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                  have hw4 : (676941261/10000000000000:ℝ) ≤ wfun (y + z) := wc_357 (y + z) (by linarith) (by linarith)
                  have hw5 : (2413024171/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_737 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                  have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                  have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                  have hw4 : (1168886057/10000000000000:ℝ) ≤ wfun (y + z) := wc_366 (y + z) (by linarith) (by linarith)
                  have hw5 : (3019797449/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_747 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                have hw2 : (38452957/2000000000000:ℝ) ≤ wfun z := wc_61 z (by linarith) (by linarith)
                have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                have hw4 : (66837841/1000000000000:ℝ) ≤ wfun (y + z) := wc_358 (y + z) (by linarith) (by linarith)
                have hw5 : (2991406031/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_748 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
              have hw2 : (4137262453/10000000000000:ℝ) ≤ wfun z := wc_66 z (by linarith) (by linarith)
              have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
              have hw4 : (1764735511/10000000000000:ℝ) ≤ wfun (y + z) := wc_370 (y + z) (by linarith) (by linarith)
              have hw5 : (1808088631/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_749 (x + y + z) (by linarith) (by linarith)
              linarith
      · have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
          rcases le_total y (2:ℝ) with hq10 | hq10
          · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
        have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
        have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
        have hw5 : (2238382569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_741 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (141/128:ℝ) with hc | hc
      · rcases le_total x (267/256:ℝ) with hc | hc
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
          have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
          have hw3 : (21491553/2500000000000:ℝ) ≤ wfun (x + y) := wc_307 (x + y) (by linarith) (by linarith)
          have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
          have hw5 : (18244153/80000000000:ℝ) ≤ wfun (x + y + z) := wc_740 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw2 : (44604923/2500000000000:ℝ) ≤ wfun z := wc_62 z (by linarith) (by linarith)
          have hw3 : (162913869/2500000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
          have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
          have hw5 : (1741738127/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_751 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw2 : (11778340313/10000000000000:ℝ) ≤ wfun z := wc_67 z (by linarith) (by linarith)
        have hw3 : (20953831/2500000000000:ℝ) ≤ wfun (x + y) := wc_308 (x + y) (by linarith) (by linarith)
        have hw4 : (5096134953/10000000000000:ℝ) ≤ wfun (y + z) := wc_384 (y + z) (by linarith) (by linarith)
        have hw5 : (600628743/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_752 (x + y + z) (by linarith) (by linarith)
        linarith

end Zeta23Ext.Bridge.FourPoint
