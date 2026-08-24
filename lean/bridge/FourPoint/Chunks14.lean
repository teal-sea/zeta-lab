import FourPoint.Cells

/-! Chunk module 14 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_12 (x y z : ℝ) (hx1 : (1063/1024:ℝ) ≤ x) (hx2 : x ≤ (267/256:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
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
    · rcases le_total y (4067/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_241 (x + y) (by linarith) (by linarith)
            have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
            have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_580 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
              have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_241 (x + y) (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
            have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_596 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
            have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
            have hw5 : (1105910359/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_596 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
            have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
            have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_609 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
              have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
              have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (4067/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
                have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4277/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4287/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                linarith
  · rcases le_total x (2131/2048:ℝ) with hc | hc
    · rcases le_total y (4067/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_241 (x + y) (by linarith) (by linarith)
            have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
            have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_609 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
              have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
              have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_241 (x + y) (by linarith) (by linarith)
            have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
            have hw5 : (659665673/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_630 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
            have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_251 (x + y) (by linarith) (by linarith)
            have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
            have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_640 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
            have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
            have hw5 : (659665673/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_630 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
              have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4257/4096:ℝ) with hc | hc
          · have hw0 : (2586175977/10000000000000:ℝ) ≤ wfun x := wc_19 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (649907/625000000000:ℝ) ≤ wfun (x + y) := wc_255 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
            have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_647 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (560227329/2500000000000:ℝ) ≤ wfun x := wc_22 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (736743/400000000000:ℝ) ≤ wfun (x + y) := wc_263 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
            have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_666 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (4067/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
              have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
              have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
              have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8129/4096:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (18448463/10000000000000:ℝ) ≤ wfun (x + y) := wc_262 (x + y) (by linarith) (by linarith)
              have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
              have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
              have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
              have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
              have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
              have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · rcases le_total z (4297/4096:ℝ) with hc | hc
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
                have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
              have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4267/4096:ℝ) with hc | hc
          · have hw0 : (1921155551/10000000000000:ℝ) ≤ wfun x := wc_23 x (by linarith) (by linarith)
            have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
            have hw5 : (775154287/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_673 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (8139/4096:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
              have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
              have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_25 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
              have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
              have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_42 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (1023/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (2041/1024:ℝ) with hc | hc
  · rcases le_total z (1073/1024:ℝ) with hc | hc
    · rcases le_total x (2141/2048:ℝ) with hc | hc
      · rcases le_total y (4077/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                  have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                  have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                  have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                  have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                  have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                  have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                  have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                  have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                  have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                  have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                  have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_324 (y + z) (by linarith) (by linarith)
                  have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                  have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                  have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                  have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_324 (y + z) (by linarith) (by linarith)
                  have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                  linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
                have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                  have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                  have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                  have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (4077/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                  have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                  have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                  have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                  have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                  have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                  have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4277/4096:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                  have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                  have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                  have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                  have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                  have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                  have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (192151891/10000000000000:ℝ) ≤ wfun (y + z) := wc_324 (y + z) (by linarith) (by linarith)
                  have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                  have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                  have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
                have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
                have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_332 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_332 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_708 (x + y + z) (by linarith) (by linarith)
                linarith
    · rcases le_total x (2141/2048:ℝ) with hc | hc
      · rcases le_total y (4077/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (5774823/625000000000:ℝ) ≤ wfun (x + y) := wc_299 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (1798491653/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_701 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_316 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_707 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_319 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (1798491653/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_701 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_707 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
            have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (4077/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_708 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_319 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_709 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_721 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (47960431/2500000000000:ℝ) ≤ wfun (x + y) := wc_325 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_709 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_331 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_721 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total z (1073/1024:ℝ) with hc | hc
    · rcases le_total x (2141/2048:ℝ) with hc | hc
      · rcases le_total y (4087/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (47960431/2500000000000:ℝ) ≤ wfun (x + y) := wc_325 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
              have hw5 : (418067961/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_687 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_331 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
              have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_698 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4277/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (47960431/2500000000000:ℝ) ≤ wfun (x + y) := wc_325 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (1798491653/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_701 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_331 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_707 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
            have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
            have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (4087/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (10193319/400000000000:ℝ) ≤ wfun (x + y) := wc_333 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
              have hw5 : (1798491653/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_701 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
              have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_707 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4287/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (10193319/400000000000:ℝ) ≤ wfun (x + y) := wc_333 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_709 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
              have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
              have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_721 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
            have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (2141/2048:ℝ) with hc | hc
      · rcases le_total y (4087/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
            have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
            have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
          have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
          have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
          have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
          have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_723 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (4087/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
            have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
            have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_725 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
          have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
          have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
          have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
          have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_726 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_43 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (1023/512:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
                  have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                  have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
                  have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                  have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                  have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
                  have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
                have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
                have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_332 (x + y) (by linarith) (by linarith)
                have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
                have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · rcases le_total z (4287/4096:ℝ) with hc | hc
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                  have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                  have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
                  have hw5 : (112675493/625000000000:ℝ) ≤ wfun (x + y + z) := wc_699 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                  have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                  have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                  have hw4 : (32783471/2000000000000:ℝ) ≤ wfun (y + z) := wc_322 (y + z) (by linarith) (by linarith)
                  have hw5 : (933826779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_705 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
                have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_332 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_708 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8159/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (2661857281/10000000000000:ℝ) ≤ wfun y := wc_132 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_332 (x + y) (by linarith) (by linarith)
                have hw4 : (4302423/312500000000:ℝ) ≤ wfun (y + z) := wc_319 (y + z) (by linarith) (by linarith)
                have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (1245909663/5000000000000:ℝ) ≤ wfun y := wc_134 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_338 (x + y) (by linarith) (by linarith)
                have hw4 : (163652657/10000000000000:ℝ) ≤ wfun (y + z) := wc_323 (y + z) (by linarith) (by linarith)
                have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
              have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
              have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_707 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (10193319/400000000000:ℝ) ≤ wfun (x + y) := wc_333 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
              have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_709 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
              have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_721 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (4077/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (255244651/10000000000000:ℝ) ≤ wfun (x + y) := wc_332 (x + y) (by linarith) (by linarith)
                have hw4 : (5774823/625000000000:ℝ) ≤ wfun (y + z) := wc_299 (y + z) (by linarith) (by linarith)
                have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (290088193/10000000000000:ℝ) ≤ wfun (x + y) := wc_338 (x + y) (by linarith) (by linarith)
                have hw4 : (569617/50000000000:ℝ) ≤ wfun (y + z) := wc_316 (y + z) (by linarith) (by linarith)
                have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
              have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
              have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_707 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (4307/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (10193319/400000000000:ℝ) ≤ wfun (x + y) := wc_333 (x + y) (by linarith) (by linarith)
              have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
              have hw5 : (964460991/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_709 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (289620509/10000000000000:ℝ) ≤ wfun (x + y) := wc_339 (x + y) (by linarith) (by linarith)
              have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
              have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_721 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
            have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
            have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4077/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · rcases le_total x (4297/4096:ℝ) with hc | hc
            · rcases le_total y (8149/4096:ℝ) with hc | hc
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (1509609143/5000000000000:ℝ) ≤ wfun y := wc_126 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                have hw4 : (47960431/2500000000000:ℝ) ≤ wfun (y + z) := wc_325 (y + z) (by linarith) (by linarith)
                have hw5 : (965616743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_708 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
                have hw1 : (354706643/1250000000000:ℝ) ≤ wfun y := wc_131 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                have hw4 : (111118793/5000000000000:ℝ) ≤ wfun (y + z) := wc_331 (y + z) (by linarith) (by linarith)
                have hw5 : (49952307/250000000000:ℝ) ≤ wfun (x + y + z) := wc_720 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_331 (x + y) (by linarith) (by linarith)
              have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
              have hw5 : (1995701471/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_721 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
            have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_725 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (4077/2048:ℝ) with hc | hc
        · rcases le_total z (2151/2048:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
            have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_725 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
          have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
          have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
          have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
          have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_726 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total z (1073/1024:ℝ) with hc | hc
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4087/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
            have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
            have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
            have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_725 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (4087/2048:ℝ) with hc | hc
        · rcases le_total z (2141/2048:ℝ) with hc | hc
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
            have hw4 : (23941523/1250000000000:ℝ) ≤ wfun (y + z) := wc_326 (y + z) (by linarith) (by linarith)
            have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
            have hw4 : (25442213/1000000000000:ℝ) ≤ wfun (y + z) := wc_334 (y + z) (by linarith) (by linarith)
            have hw5 : (1099796941/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_725 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
          have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
          have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
          have hw4 : (63400731/2500000000000:ℝ) ≤ wfun (y + z) := wc_335 (y + z) (by linarith) (by linarith)
          have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_726 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total x (2151/2048:ℝ) with hc | hc
      · rcases le_total y (4087/2048:ℝ) with hc | hc
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
          have hw1 : (1084176557/5000000000000:ℝ) ≤ wfun y := wc_135 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
          have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
          have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_341 (y + z) (by linarith) (by linarith)
          have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_726 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
          have hw1 : (1868712167/10000000000000:ℝ) ≤ wfun y := wc_137 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
          have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
          have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
          have hw5 : (2336612903/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_731 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
        have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
        have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
        have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
        have hw5 : (291380049/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_732 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_50 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (131/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (17/16:ℝ) with hc | hc
  · rcases le_total y (17/8:ℝ) with hc | hc
    · rcases le_total z (17/16:ℝ) with hc | hc
      · rcases le_total x (131/128:ℝ) with hc | hc
        · rcases le_total y (267/128:ℝ) with hc | hc
          · rcases le_total z (131/128:ℝ) with hc | hc
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw1 : (18186303/400000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
              have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
                rcases le_total z (1:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
              have hw3 : (20953831/2500000000000:ℝ) ≤ wfun (x + y) := wc_308 (x + y) (by linarith) (by linarith)
              have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
              have hw5 : (58303/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_458 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
                rcases le_total x (1:ℝ) with hq00 | hq00
                · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
              have hw1 : (18186303/400000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
              have hw3 : (20953831/2500000000000:ℝ) ≤ wfun (x + y) := wc_308 (x + y) (by linarith) (by linarith)
              have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (913271/15625000000:ℝ) ≤ wfun (x + y + z) := wc_554 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
              rcases le_total x (1:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
            have hw1 : (4789633321/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (563044583/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_555 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (267/128:ℝ) with hc | hc
          · rcases le_total z (131/128:ℝ) with hc | hc
            · have hw1 : (18186303/400000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
              have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
                rcases le_total z (1:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
              have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (20953831/2500000000000:ℝ) ≤ wfun (y + z) := wc_308 (y + z) (by linarith) (by linarith)
              have hw5 : (913271/15625000000:ℝ) ≤ wfun (x + y + z) := wc_554 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (18186303/400000000000:ℝ) ≤ wfun y := wc_156 y (by linarith) (by linarith)
              have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
              have hw4 : (419583999/2500000000000:ℝ) ≤ wfun (y + z) := wc_372 (y + z) (by linarith) (by linarith)
              have hw5 : (2238382569/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_741 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (4789633321/10000000000000:ℝ) ≤ wfun y := wc_172 y (by linarith) (by linarith)
            have hw3 : (5096134953/10000000000000:ℝ) ≤ wfun (x + y) := wc_384 (x + y) (by linarith) (by linarith)
            have hw4 : (798582451/5000000000000:ℝ) ≤ wfun (y + z) := wc_374 (y + z) (by linarith) (by linarith)
            have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_742 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw1 : (42177537/1000000000000:ℝ) ≤ wfun y := wc_158 y (by linarith) (by linarith)
        have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
        have hw3 : (75856633/10000000000000:ℝ) ≤ wfun (x + y) := wc_311 (x + y) (by linarith) (by linarith)
        have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_386 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_389 (y + z) (by linarith) (by linarith))
        have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_742 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_757 (x + y + z) (by linarith) (by linarith))
        linarith
    · have hw1 : (48584483/40000000000:ℝ) ≤ wfun y := wc_178 y (by linarith) (by linarith)
      have hw3 : (589186081/1250000000000:ℝ) ≤ wfun (x + y) := by
        rcases le_total (x + y) (13/4:ℝ) with hq30 | hq30
        · exact le_trans (by norm_num) (wc_386 (x + y) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_389 (x + y) (by linarith) (by linarith))
      have hw4 : (589186081/1250000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_386 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_392 (y + z) (by linarith) (by linarith))
      have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := by
        rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
        · exact le_trans (by norm_num) (wc_742 (x + y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_758 (x + y + z) (by linarith) (by linarith))
      linarith
  · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
    have hw1 : (182240171/5000000000000:ℝ) ≤ wfun y := wc_160 y (by linarith) (by linarith)
    have hw3 : (589186081/1250000000000:ℝ) ≤ wfun (x + y) := by
      rcases le_total (x + y) (13/4:ℝ) with hq30 | hq30
      · exact le_trans (by norm_num) (wc_386 (x + y) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_392 (x + y) (by linarith) (by linarith))
    have hw4 : (17540223/2500000000000:ℝ) ≤ wfun (y + z) := by
      rcases le_total (y + z) (13/4:ℝ) with hq40 | hq40
      · exact le_trans (by norm_num) (wc_312 (y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_392 (y + z) (by linarith) (by linarith))
    have hw5 : (2156990541/10000000000000:ℝ) ≤ wfun (x + y + z) := by
      rcases le_total (x + y + z) (17/4:ℝ) with hq50 | hq50
      · exact le_trans (by norm_num) (wc_742 (x + y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_760 (x + y + z) (by linarith) (by linarith))
    linarith

end Zeta23Ext.Bridge.FourPoint
