import FourPoint.Cells

/-! Chunk module 3 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_24 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (2021/1024:ℝ) ≤ y) (hy2 : y ≤ (1013/512:ℝ))
    (hz1 : (1073/1024:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (2141/2048:ℝ) with hc | hc
  · rcases le_total y (4047/2048:ℝ) with hc | hc
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_236 (x + y) (by linarith) (by linarith)
            have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
            have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
            have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
            have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (278293/2500000000000:ℝ) ≤ wfun (x + y) := wc_236 (x + y) (by linarith) (by linarith)
            have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
            have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
            have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
            have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
            have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (1108574073/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_594 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8559/8192:ℝ) with hc | hc
              · have hw0 : (1232162133/10000000000000:ℝ) ≤ wfun x := wc_32 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_239 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_34 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_248 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_617 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4277/4096:ℝ) with hc | hc
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
            have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (135743827/1000000000000:ℝ) ≤ wfun x := wc_27 x (by linarith) (by linarith)
            have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
            have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
            have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
            have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
            have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
            have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_33 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total y (4047/2048:ℝ) with hc | hc
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
            have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (1185403/10000000000000:ℝ) ≤ wfun (y + z) := wc_240 (y + z) (by linarith) (by linarith)
              have hw5 : (290097117/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_602 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (931809/2000000000000:ℝ) ≤ wfun (y + z) := wc_250 (y + z) (by linarith) (by linarith)
              have hw5 : (1213318631/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_607 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
              have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
            have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
            have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
            have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (8089/4096:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
            have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
            have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
            have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
            have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total z (2151/2048:ℝ) with hc | hc
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (593183/5000000000000:ℝ) ≤ wfun (x + y) := wc_239 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (303512103/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_606 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (2638657/10000000000000:ℝ) ≤ wfun (x + y) := wc_248 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (124094633/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_617 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (1267359331/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_620 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_249 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_252 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_624 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8569/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_249 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_252 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (4662827/10000000000000:ℝ) ≤ wfun (x + y) := wc_249 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (634060693/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_619 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (7258139/10000000000000:ℝ) ≤ wfun (x + y) := wc_252 (x + y) (by linarith) (by linarith)
                have hw4 : (10415393/10000000000000:ℝ) ≤ wfun (y + z) := wc_254 (y + z) (by linarith) (by linarith)
                have hw5 : (647786457/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_624 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4297/4096:ℝ) with hc | hc
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (65990561/1250000000000:ℝ) ≤ wfun z := wc_43 z (by linarith) (by linarith)
                have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                have hw4 : (18448463/10000000000000:ℝ) ≤ wfun (y + z) := wc_262 (y + z) (by linarith) (by linarith)
                have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total x (8579/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (5211923/5000000000000:ℝ) ≤ wfun (x + y) := wc_253 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_48 z (by linarith) (by linarith)
                have hw3 : (3539799/2500000000000:ℝ) ≤ wfun (x + y) := wc_259 (x + y) (by linarith) (by linarith)
                have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
                have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total x (4287/4096:ℝ) with hc | hc
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (52900211/400000000000:ℝ) ≤ wfun (x + y + z) := wc_628 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total y (8099/4096:ℝ) with hc | hc
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (275750223/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_638 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total z (4307/4096:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (259133459/10000000000000:ℝ) ≤ wfun z := wc_50 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (718045723/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_645 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
              have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_52 z (by linarith) (by linarith)
              have hw3 : (10415393/10000000000000:ℝ) ≤ wfun (x + y) := wc_254 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
              linarith

set_option maxHeartbeats 20000000 in
lemma ch_38 (x y z : ℝ) (hx1 : (539/512:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (1013/512:ℝ) with hc | hc
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2021/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4037/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                  have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
                  have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                  have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                  have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
                  have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                  have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4037/2048:ℝ) with hc | hc
              · have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_232 (y + z) (by linarith) (by linarith)
                have hw5 : (55096489/500000000000:ℝ) ≤ wfun (x + y + z) := wc_598 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_611 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4037/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                have hw5 : (1206050917/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_611 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                  have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                  have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_631 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                  have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                  have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_648 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4037/2048:ℝ) with hc | hc
              · have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                have hw5 : (262917659/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_632 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_649 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                    have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
                    have hw5 : (121040499/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_609 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_279 (x + y) (by linarith) (by linarith)
                    have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_622 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8089/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (2825867677/5000000000000:ℝ) ≤ wfun y := wc_94 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (3594019/1250000000000:ℝ) ≤ wfun (x + y) := wc_268 (x + y) (by linarith) (by linarith)
                      have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (337510039/625000000000:ℝ) ≤ wfun y := wc_97 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (8264047/2000000000000:ℝ) ≤ wfun (x + y) := wc_278 (x + y) (by linarith) (by linarith)
                      have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
                      have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_279 (x + y) (by linarith) (by linarith)
                    have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_640 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8099/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                      have hw5 : (660458559/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_629 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                      have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
                      have hw5 : (172136989/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_639 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_293 (x + y) (by linarith) (by linarith)
                    have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_640 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8099/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                      have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
                      have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                      have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
                      have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_293 (x + y) (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                    have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_666 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                  have hw5 : (263549591/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_631 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                  have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_648 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                  have hw5 : (715464319/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_648 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                  have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                    have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw3 : (2870559/1000000000000:ℝ) ≤ wfun (x + y) := wc_269 (x + y) (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                    have hw5 : (1432646991/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_647 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw3 : (20626673/5000000000000:ℝ) ≤ wfun (x + y) := wc_279 (x + y) (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                    have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_666 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8099/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (1030893657/2000000000000:ℝ) ≤ wfun y := wc_98 y (by linarith) (by linarith)
                      have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                      have hw3 : (11229273/2000000000000:ℝ) ≤ wfun (x + y) := wc_284 (x + y) (by linarith) (by linarith)
                      have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
                      have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (2457325291/5000000000000:ℝ) ≤ wfun y := wc_100 y (by linarith) (by linarith)
                      have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                      have hw3 : (73224081/10000000000000:ℝ) ≤ wfun (x + y) := wc_292 (x + y) (by linarith) (by linarith)
                      have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
                      have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw3 : (18276411/2500000000000:ℝ) ≤ wfun (x + y) := wc_293 (x + y) (by linarith) (by linarith)
                    have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                    have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_682 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                  have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                  have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_688 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_243 (y + z) (by linarith) (by linarith)
                have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_675 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_257 (y + z) (by linarith) (by linarith)
                have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_689 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (2021/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
            have hw5 : (600137957/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_613 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
            have hw5 : (1420672477/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_651 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2171/2048:ℝ) with hc | hc
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_649 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_675 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (5858063/1000000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
              have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_321 (x + y) (by linarith) (by linarith)
              have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_676 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
            have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
            have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2021/1024:ℝ) with hc | hc
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4037/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
                have hw3 : (1181561/10000000000000:ℝ) ≤ wfun (x + y) := wc_242 (x + y) (by linarith) (by linarith)
                have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_243 (y + z) (by linarith) (by linarith)
                have hw5 : (1427499659/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_649 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
                have hw3 : (2076333/2000000000000:ℝ) ≤ wfun (x + y) := wc_256 (x + y) (by linarith) (by linarith)
                have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_257 (y + z) (by linarith) (by linarith)
                have hw5 : (1544741841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_675 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
              have hw3 : (5174037/5000000000000:ℝ) ≤ wfun (x + y) := wc_257 (x + y) (by linarith) (by linarith)
              have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
              have hw5 : (1541044571/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_676 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
            have hw3 : (293481/2500000000000:ℝ) ≤ wfun (x + y) := wc_244 (x + y) (by linarith) (by linarith)
            have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
            have hw5 : (1658311191/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_691 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4047/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (107907129/200000000000:ℝ) ≤ wfun y := wc_95 y (by linarith) (by linarith)
                have hw3 : (14329561/5000000000000:ℝ) ≤ wfun (x + y) := wc_270 (x + y) (by linarith) (by linarith)
                have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_271 (y + z) (by linarith) (by linarith)
                have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_689 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (1227632877/2500000000000:ℝ) ≤ wfun y := wc_99 y (by linarith) (by linarith)
                have hw3 : (55964847/10000000000000:ℝ) ≤ wfun (x + y) := wc_286 (x + y) (by linarith) (by linarith)
                have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_287 (y + z) (by linarith) (by linarith)
                have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_703 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
              have hw3 : (27892031/5000000000000:ℝ) ≤ wfun (x + y) := wc_287 (x + y) (by linarith) (by linarith)
              have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
              have hw5 : (1787757479/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_704 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
            have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
            have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (2021/1024:ℝ) with hc | hc
        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
          have hw1 : (2946158453/5000000000000:ℝ) ≤ wfun y := wc_87 y (by linarith) (by linarith)
          have hw3 : (28474189/10000000000000:ℝ) ≤ wfun (x + y) := wc_272 (x + y) (by linarith) (by linarith)
          have hw4 : (1166349/10000000000000:ℝ) ≤ wfun (y + z) := wc_245 (y + z) (by linarith) (by linarith)
          have hw5 : (12893743/78125000000:ℝ) ≤ wfun (x + y + z) := wc_692 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
          have hw1 : (4902043129/10000000000000:ℝ) ≤ wfun y := wc_96 y (by linarith) (by linarith)
          have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
          have hw4 : (28290747/10000000000000:ℝ) ≤ wfun (y + z) := wc_273 (y + z) (by linarith) (by linarith)
          have hw5 : (951861201/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_714 (x + y + z) (by linarith) (by linarith)
          linarith
  · rcases le_total z (539/512:ℝ) with hc | hc
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8109/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                      have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
                      have hw5 : (57374717/400000000000:ℝ) ≤ wfun (x + y + z) := wc_646 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                      have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
                      have hw5 : (1492727701/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_665 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_316 (x + y) (by linarith) (by linarith)
                    have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                    have hw5 : (298187457/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_666 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8109/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                      have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
                      have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                      have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
                      have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_316 (x + y) (by linarith) (by linarith)
                    have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                    have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_682 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8119/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                      have hw4 : (649907/625000000000:ℝ) ≤ wfun (y + z) := wc_255 (y + z) (by linarith) (by linarith)
                      have hw5 : (62086789/400000000000:ℝ) ≤ wfun (x + y + z) := wc_672 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                      have hw4 : (736743/400000000000:ℝ) ≤ wfun (y + z) := wc_263 (y + z) (by linarith) (by linarith)
                      have hw5 : (322537687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_681 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
                    have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                    have hw5 : (1610755299/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_682 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8119/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (1057590771/2500000000000:ℝ) ≤ wfun y := wc_111 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
                      have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
                      have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (4013960191/10000000000000:ℝ) ≤ wfun y := wc_115 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (32783471/2000000000000:ℝ) ≤ wfun (x + y) := wc_322 (x + y) (by linarith) (by linarith)
                      have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
                      have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
                    have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                    have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_698 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                  have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
                  have hw5 : (1548450213/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_674 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                  have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_688 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                  have hw4 : (2076333/2000000000000:ℝ) ≤ wfun (y + z) := wc_256 (y + z) (by linarith) (by linarith)
                  have hw5 : (1670268489/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_688 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                  have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                  have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
                  linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8109/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (4680699447/10000000000000:ℝ) ≤ wfun y := wc_102 y (by linarith) (by linarith)
                      have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                      have hw3 : (46273399/5000000000000:ℝ) ≤ wfun (x + y) := wc_298 (x + y) (by linarith) (by linarith)
                      have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
                      have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (4452606511/10000000000000:ℝ) ≤ wfun y := wc_108 y (by linarith) (by linarith)
                      have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                      have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
                      have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
                      have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw3 : (569617/50000000000:ℝ) ≤ wfun (x + y) := wc_316 (x + y) (by linarith) (by linarith)
                    have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                    have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_698 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                  have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                  have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                    have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw3 : (4302423/312500000000:ℝ) ≤ wfun (x + y) := wc_319 (x + y) (by linarith) (by linarith)
                    have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                    have hw5 : (1798491653/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_701 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                    have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                    have hw3 : (163652657/10000000000000:ℝ) ≤ wfun (x + y) := wc_323 (x + y) (by linarith) (by linarith)
                    have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                    have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_707 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                  have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                  have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                have hw4 : (7141617/2500000000000:ℝ) ≤ wfun (y + z) := wc_271 (y + z) (by linarith) (by linarith)
                have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_703 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_287 (y + z) (by linarith) (by linarith)
                have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_711 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8129/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                      have hw4 : (2870559/1000000000000:ℝ) ≤ wfun (y + z) := wc_269 (y + z) (by linarith) (by linarith)
                      have hw5 : (334855641/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_686 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                      have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                      have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                      have hw4 : (20626673/5000000000000:ℝ) ≤ wfun (y + z) := wc_279 (y + z) (by linarith) (by linarith)
                      have hw5 : (434233339/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_697 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                    have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                    have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_331 (x + y) (by linarith) (by linarith)
                    have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                    have hw5 : (867426269/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_698 (x + y + z) (by linarith) (by linarith)
                    linarith
                · rcases le_total x (4317/4096:ℝ) with hc | hc
                  · rcases le_total y (8129/4096:ℝ) with hc | hc
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (192151891/10000000000000:ℝ) ≤ wfun (x + y) := wc_324 (x + y) (by linarith) (by linarith)
                      have hw4 : (28027757/5000000000000:ℝ) ≤ wfun (y + z) := wc_285 (y + z) (by linarith) (by linarith)
                      have hw5 : (1800648153/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_700 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (85656967/10000000000000:ℝ) ≤ wfun x := wc_53 x (by linarith) (by linarith)
                      have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
                      have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                      have hw3 : (890387/40000000000:ℝ) ≤ wfun (x + y) := wc_330 (x + y) (by linarith) (by linarith)
                      have hw4 : (18276411/2500000000000:ℝ) ≤ wfun (y + z) := wc_293 (y + z) (by linarith) (by linarith)
                      have hw5 : (1865416811/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_706 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_55 x (by linarith) (by linarith)
                    have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                    have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                    have hw3 : (111118793/5000000000000:ℝ) ≤ wfun (x + y) := wc_331 (x + y) (by linarith) (by linarith)
                    have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                    have hw5 : (1863183413/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_707 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                  have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                  have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                  have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                  have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · rcases le_total z (2141/2048:ℝ) with hc | hc
                · have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                  have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                  have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                  have hw4 : (14329561/5000000000000:ℝ) ≤ wfun (y + z) := wc_270 (y + z) (by linarith) (by linarith)
                  have hw5 : (1796338383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_702 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                  have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                  have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                  have hw4 : (55964847/10000000000000:ℝ) ≤ wfun (y + z) := wc_286 (y + z) (by linarith) (by linarith)
                  have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                have hw4 : (27892031/5000000000000:ℝ) ≤ wfun (y + z) := wc_287 (y + z) (by linarith) (by linarith)
                have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_711 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · rcases le_total z (2151/2048:ℝ) with hc | hc
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                  have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                  have hw4 : (92247841/10000000000000:ℝ) ≤ wfun (y + z) := wc_300 (y + z) (by linarith) (by linarith)
                  have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                  have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
                  have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                  have hw4 : (13745521/1000000000000:ℝ) ≤ wfun (y + z) := wc_320 (y + z) (by linarith) (by linarith)
                  have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_321 (y + z) (by linarith) (by linarith)
                have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_723 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (4067/2048:ℝ) with hc | hc
              · have hw1 : (71925891/200000000000:ℝ) ≤ wfun y := wc_119 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_301 (y + z) (by linarith) (by linarith)
                have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_723 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw1 : (3204719257/10000000000000:ℝ) ≤ wfun y := wc_124 y (by linarith) (by linarith)
                have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_321 (y + z) (by linarith) (by linarith)
                have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_726 (x + y + z) (by linarith) (by linarith)
                linarith
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · rcases le_total x (2171/2048:ℝ) with hc | hc
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
                have hw4 : (235547/2000000000000:ℝ) ≤ wfun (y + z) := wc_243 (y + z) (by linarith) (by linarith)
                have hw5 : (1666270777/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_689 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (875097/10000000000000:ℝ) ≤ wfun x := wc_56 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                have hw3 : (25442213/1000000000000:ℝ) ≤ wfun (x + y) := wc_334 (x + y) (by linarith) (by linarith)
                have hw4 : (5174037/5000000000000:ℝ) ≤ wfun (y + z) := wc_257 (y + z) (by linarith) (by linarith)
                have hw5 : (1792041507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_703 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (5858063/1000000000000:ℝ) ≤ wfun x := wc_58 x (by linarith) (by linarith)
              have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
              have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
              have hw4 : (293481/2500000000000:ℝ) ≤ wfun (y + z) := wc_244 (y + z) (by linarith) (by linarith)
              have hw5 : (1787757479/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_704 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
            have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
            have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total z (1073/1024:ℝ) with hc | hc
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
            have hw4 : (28474189/10000000000000:ℝ) ≤ wfun (y + z) := wc_272 (y + z) (by linarith) (by linarith)
            have hw5 : (1912837973/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_713 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
            have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
            have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
            have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (1083/1024:ℝ) with hc | hc
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · rcases le_total z (1083/1024:ℝ) with hc | hc
          · rcases le_total x (2161/2048:ℝ) with hc | hc
            · rcases le_total y (4057/2048:ℝ) with hc | hc
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (2224562793/5000000000000:ℝ) ≤ wfun y := wc_103 y (by linarith) (by linarith)
                have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
                have hw4 : (22987523/2500000000000:ℝ) ≤ wfun (y + z) := wc_301 (y + z) (by linarith) (by linarith)
                have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_711 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (6838799/2000000000000:ℝ) ≤ wfun x := wc_54 x (by linarith) (by linarith)
                have hw1 : (2005535413/5000000000000:ℝ) ≤ wfun y := wc_112 y (by linarith) (by linarith)
                have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
                have hw4 : (2140811/156250000000:ℝ) ≤ wfun (y + z) := wc_321 (y + z) (by linarith) (by linarith)
                have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_723 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
              have hw3 : (2140811/156250000000:ℝ) ≤ wfun (x + y) := wc_321 (x + y) (by linarith) (by linarith)
              have hw4 : (11456693/1250000000000:ℝ) ≤ wfun (y + z) := wc_302 (y + z) (by linarith) (by linarith)
              have hw5 : (410242943/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_724 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
            have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
            have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
            have hw4 : (190300253/10000000000000:ℝ) ≤ wfun (y + z) := wc_328 (y + z) (by linarith) (by linarith)
            have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
          have hw5 : (271686247/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_729 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total y (2031/1024:ℝ) with hc | hc
        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
          have hw1 : (200253263/500000000000:ℝ) ≤ wfun y := wc_104 y (by linarith) (by linarith)
          have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
          have hw4 : (91064031/10000000000000:ℝ) ≤ wfun (y + z) := wc_303 (y + z) (by linarith) (by linarith)
          have hw5 : (271686247/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_729 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
          have hw1 : (400103387/1250000000000:ℝ) ≤ wfun y := wc_120 y (by linarith) (by linarith)
          have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
          have hw4 : (189078223/10000000000000:ℝ) ≤ wfun (y + z) := wc_329 (y + z) (by linarith) (by linarith)
          have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_734 (x + y + z) (by linarith) (by linarith)
          linarith

set_option maxHeartbeats 20000000 in
lemma ch_45 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (1023/512:ℝ) ≤ y) (hy2 : y ≤ (257/128:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (539/512:ℝ) with hc | hc
  · rcases le_total x (1073/1024:ℝ) with hc | hc
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · rcases le_total z (1073/1024:ℝ) with hc | hc
        · rcases le_total x (2141/2048:ℝ) with hc | hc
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · rcases le_total z (2141/2048:ℝ) with hc | hc
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                have hw4 : (326066581/10000000000000:ℝ) ≤ wfun (y + z) := wc_340 (y + z) (by linarith) (by linarith)
                have hw5 : (963306969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_710 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
                have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                  rcases le_total y (2:ℝ) with hq10 | hq10
                  · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
                have hw3 : (326066581/10000000000000:ℝ) ≤ wfun (x + y) := wc_340 (x + y) (by linarith) (by linarith)
                have hw4 : (406405247/10000000000000:ℝ) ≤ wfun (y + z) := wc_346 (y + z) (by linarith) (by linarith)
                have hw5 : (2061048329/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_722 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
              have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
              have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
              have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_723 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (4097/2048:ℝ) with hc | hc
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1591808227/10000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_139 y (by linarith) (by linarith))
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
              have hw3 : (406405247/10000000000000:ℝ) ≤ wfun (x + y) := wc_346 (x + y) (by linarith) (by linarith)
              have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_341 (y + z) (by linarith) (by linarith)
              have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_723 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
              have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := wc_142 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
              have hw3 : (495376037/10000000000000:ℝ) ≤ wfun (x + y) := wc_348 (x + y) (by linarith) (by linarith)
              have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
              have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_726 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (2141/2048:ℝ) with hc | hc
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (325017537/10000000000000:ℝ) ≤ wfun (x + y) := wc_341 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
            have hw5 : (2189105517/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_727 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
            have hw3 : (405098789/10000000000000:ℝ) ≤ wfun (x + y) := wc_347 (x + y) (by linarith) (by linarith)
            have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
            have hw5 : (291380049/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_732 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (1073/1024:ℝ) with hc | hc
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
          have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
          have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
          have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
          have hw4 : (694482783/10000000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
          have hw5 : (3861047/15625000000:ℝ) ≤ wfun (x + y + z) := wc_733 (x + y + z) (by linarith) (by linarith)
          linarith
    · rcases le_total y (2051/1024:ℝ) with hc | hc
      · rcases le_total z (1073/1024:ℝ) with hc | hc
        · rcases le_total x (2151/2048:ℝ) with hc | hc
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw3 : (493784853/10000000000000:ℝ) ≤ wfun (x + y) := wc_349 (x + y) (by linarith) (by linarith)
            have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
            have hw5 : (2189105517/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_727 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
            have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
              rcases le_total y (2:ℝ) with hq10 | hq10
              · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
            have hw3 : (295506067/5000000000000:ℝ) ≤ wfun (x + y) := wc_353 (x + y) (by linarith) (by linarith)
            have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
            have hw5 : (291380049/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_732 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
          have hw1 : (1337086167/10000000000000:ℝ) ≤ wfun y := by
            rcases le_total y (2:ℝ) with hq10 | hq10
            · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_140 y (by linarith) (by linarith))
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
          have hw3 : (24610003/500000000000:ℝ) ≤ wfun (x + y) := wc_350 (x + y) (by linarith) (by linarith)
          have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
          have hw5 : (3861047/15625000000:ℝ) ≤ wfun (x + y + z) := wc_733 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
        have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := wc_143 y (by linarith) (by linarith)
        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
        have hw3 : (694482783/10000000000000:ℝ) ≤ wfun (x + y) := wc_354 (x + y) (by linarith) (by linarith)
        have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
        have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_734 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total x (1073/1024:ℝ) with hc | hc
    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
        rcases le_total y (2:ℝ) with hq10 | hq10
        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
      have hw3 : (160947823/5000000000000:ℝ) ≤ wfun (x + y) := wc_343 (x + y) (by linarith) (by linarith)
      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
      have hw5 : (2447644383/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_735 (x + y + z) (by linarith) (by linarith)
      linarith
    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
        rcases le_total y (2:ℝ) with hq10 | hq10
        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
      have hw3 : (489049523/10000000000000:ℝ) ≤ wfun (x + y) := wc_351 (x + y) (by linarith) (by linarith)
      have hw4 : (685641829/10000000000000:ℝ) ≤ wfun (y + z) := wc_356 (y + z) (by linarith) (by linarith)
      have hw5 : (549546581/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_744 (x + y + z) (by linarith) (by linarith)
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_57 (x y z : ℝ) (hx1 : (17/16:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (131/64:ℝ))
    (hz1 : (121/64:ℝ) ≤ z) (hz2 : z ≤ (131/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (63/32:ℝ) with hc | hc
  · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
    have hw1 : (795663039/1250000000000:ℝ) ≤ wfun y := wc_76 y (by linarith) (by linarith)
    linarith
  · rcases le_total z (63/32:ℝ) with hc | hc
    · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
      have hw2 : (795663039/1250000000000:ℝ) ≤ wfun z := wc_76 z (by linarith) (by linarith)
      have hw3 : (75856633/10000000000000:ℝ) ≤ wfun (x + y) := wc_311 (x + y) (by linarith) (by linarith)
      linarith
    · rcases le_total x (141/128:ℝ) with hc | hc
      · rcases le_total y (257/128:ℝ) with hc | hc
        · rcases le_total z (257/128:ℝ) with hc | hc
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total y (509/256:ℝ) with hc | hc
              · rcases le_total z (509/256:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
                  have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                  have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
                  have hw4 : (319416431/5000000000000:ℝ) ≤ wfun (y + z) := wc_405 (y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
                  have hw4 : (31317919/2000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
                  have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_771 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (509/256:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                  have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                  have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                  have hw4 : (31317919/2000000000000:ℝ) ≤ wfun (y + z) := wc_410 (y + z) (by linarith) (by linarith)
                  have hw5 : (1405331/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_771 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1023/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                      have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_419 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                      have hw5 : (190040129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_808 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                      have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                        rcases le_total z (2:ℝ) with hq20 | hq20
                        · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                      have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                      have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                    have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                      rcases le_total z (2:ℝ) with hq20 | hq20
                      · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                    have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_366 (x + y) (by linarith) (by linarith)
                    have hw5 : (43578037/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
                    linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
              have hw3 : (162913869/2500000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
              have hw5 : (6814137/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_773 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total y (509/256:ℝ) with hc | hc
              · rcases le_total z (519/256:ℝ) with hc | hc
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1013/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (4884069333/10000000000000:ℝ) ≤ wfun y := wc_88 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                      have hw3 : (18095851/2000000000000:ℝ) ≤ wfun (x + y) := wc_304 (x + y) (by linarith) (by linarith)
                      have hw4 : (19058233/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_419 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_435 (y + z) (by linarith) (by linarith))
                      have hw5 : (190040129/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_808 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (3192232409/10000000000000:ℝ) ≤ wfun y := wc_105 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                      have hw3 : (63967043/2000000000000:ℝ) ≤ wfun (x + y) := wc_344 (x + y) (by linarith) (by linarith)
                      have hw5 : (43914233/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_846 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                    have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw3 : (157881813/5000000000000:ℝ) ≤ wfun (x + y) := wc_345 (x + y) (by linarith) (by linarith)
                    have hw5 : (43578037/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_847 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (396477691/1250000000000:ℝ) ≤ wfun y := wc_89 y (by linarith) (by linarith)
                  have hw3 : (88186617/10000000000000:ℝ) ≤ wfun (x + y) := wc_306 (x + y) (by linarith) (by linarith)
                  have hw5 : (551493311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (519/256:ℝ) with hc | hc
                · rcases le_total x (549/512:ℝ) with hc | hc
                  · rcases le_total y (1023/512:ℝ) with hc | hc
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (1865845891/10000000000000:ℝ) ≤ wfun y := wc_129 y (by linarith) (by linarith)
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                      have hw3 : (685641829/10000000000000:ℝ) ≤ wfun (x + y) := wc_356 (x + y) (by linarith) (by linarith)
                      have hw5 : (560010683/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_881 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (9984781/500000000000:ℝ) ≤ wfun x := wc_60 x (by linarith) (by linarith)
                      have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                        rcases le_total y (2:ℝ) with hq10 | hq10
                        · exact le_trans (by norm_num) (wc_138 y (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                      have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                      have hw3 : (591930551/5000000000000:ℝ) ≤ wfun (x + y) := wc_365 (x + y) (by linarith) (by linarith)
                      have hw5 : (814792219/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_922 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · have hw0 : (1609622259/10000000000000:ℝ) ≤ wfun x := wc_65 x (by linarith) (by linarith)
                    have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                      rcases le_total y (2:ℝ) with hq10 | hq10
                      · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                    have hw2 : (13164037/10000000000000:ℝ) ≤ wfun z := wc_146 z (by linarith) (by linarith)
                    have hw3 : (1168886057/10000000000000:ℝ) ≤ wfun (x + y) := wc_366 (x + y) (by linarith) (by linarith)
                    have hw5 : (404289107/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_923 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                    rcases le_total y (2:ℝ) with hq10 | hq10
                    · exact le_trans (by norm_num) (wc_130 y (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
                  have hw3 : (66837841/1000000000000:ℝ) ≤ wfun (x + y) := wc_358 (x + y) (by linarith) (by linarith)
                  have hw4 : (31471/5000000000000:ℝ) ≤ wfun (y + z) := wc_453 (y + z) (by linarith) (by linarith)
                  have hw5 : (1097277581/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_947 (x + y + z) (by linarith) (by linarith)
                  linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw1 : (179073511/2000000000000:ℝ) ≤ wfun y := by
                rcases le_total y (2:ℝ) with hq10 | hq10
                · exact le_trans (by norm_num) (wc_90 y (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 y (by linarith) (by linarith))
              have hw3 : (162913869/2500000000000:ℝ) ≤ wfun (x + y) := wc_360 (x + y) (by linarith) (by linarith)
              have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (257/128:ℝ) with hc | hc
          · rcases le_total x (277/256:ℝ) with hc | hc
            · rcases le_total y (519/256:ℝ) with hc | hc
              · rcases le_total z (509/256:ℝ) with hc | hc
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                  have hw2 : (396477691/1250000000000:ℝ) ≤ wfun z := wc_89 z (by linarith) (by linarith)
                  have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
                  have hw5 : (187138697/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_810 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                  have hw1 : (13164037/10000000000000:ℝ) ≤ wfun y := wc_146 y (by linarith) (by linarith)
                  have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                    rcases le_total z (2:ℝ) with hq20 | hq20
                    · exact le_trans (by norm_num) (wc_130 z (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                  have hw3 : (1764735511/10000000000000:ℝ) ≤ wfun (x + y) := wc_370 (x + y) (by linarith) (by linarith)
                  have hw5 : (551493311/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_883 (x + y + z) (by linarith) (by linarith)
                  linarith
              · have hw0 : (38452957/2000000000000:ℝ) ≤ wfun x := wc_61 x (by linarith) (by linarith)
                have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                  rcases le_total z (2:ℝ) with hq20 | hq20
                  · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
                have hw3 : (1670535297/5000000000000:ℝ) ≤ wfun (x + y) := wc_378 (x + y) (by linarith) (by linarith)
                have hw5 : (108627463/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_884 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (4137262453/10000000000000:ℝ) ≤ wfun x := wc_66 x (by linarith) (by linarith)
              have hw2 : (179073511/2000000000000:ℝ) ≤ wfun z := by
                rcases le_total z (2:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_90 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_141 z (by linarith) (by linarith))
              have hw3 : (1629257293/5000000000000:ℝ) ≤ wfun (x + y) := wc_379 (x + y) (by linarith) (by linarith)
              have hw5 : (534939039/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_885 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (44604923/2500000000000:ℝ) ≤ wfun x := wc_62 x (by linarith) (by linarith)
            have hw3 : (419583999/2500000000000:ℝ) ≤ wfun (x + y) := wc_372 (x + y) (by linarith) (by linarith)
            have hw4 : (60567/10000000000000:ℝ) ≤ wfun (y + z) := wc_456 (y + z) (by linarith) (by linarith)
            have hw5 : (1048517003/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_949 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (11778340313/10000000000000:ℝ) ≤ wfun x := wc_67 x (by linarith) (by linarith)
        have hw3 : (798582451/5000000000000:ℝ) ≤ wfun (x + y) := wc_374 (x + y) (by linarith) (by linarith)
        have hw5 : (168305763/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_814 (x + y + z) (by linarith) (by linarith)
        linarith

set_option maxHeartbeats 20000000 in
lemma ch_66 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (389/128:ℝ) ≤ y) (hy2 : y ≤ (105/32:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (73/64:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (809/256:ℝ) with hc | hc
  · rcases le_total x (17/16:ℝ) with hc | hc
    · rcases le_total z (17/16:ℝ) with hc | hc
      · rcases le_total y (1587/512:ℝ) with hc | hc
        · rcases le_total x (131/128:ℝ) with hc | hc
          · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
              rcases le_total x (1:ℝ) with hq00 | hq00
              · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
            have hw1 : (249212333/10000000000000:ℝ) ≤ wfun y := wc_336 y (by linarith) (by linarith)
            have hw3 : (13104471/5000000000000:ℝ) ≤ wfun (x + y) := wc_485 (x + y) (by linarith) (by linarith)
            have hw4 : (25235977/10000000000000:ℝ) ≤ wfun (y + z) := wc_486 (y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total z (131/128:ℝ) with hc | hc
            · have hw1 : (249212333/10000000000000:ℝ) ≤ wfun y := wc_336 y (by linarith) (by linarith)
              have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
                rcases le_total z (1:ℝ) with hq20 | hq20
                · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
              have hw3 : (848165913/10000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
              have hw4 : (13104471/5000000000000:ℝ) ≤ wfun (y + z) := wc_485 (y + z) (by linarith) (by linarith)
              have hw5 : (72912521/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_837 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw1 : (249212333/10000000000000:ℝ) ≤ wfun y := wc_336 y (by linarith) (by linarith)
              have hw3 : (848165913/10000000000000:ℝ) ≤ wfun (x + y) := wc_574 (x + y) (by linarith) (by linarith)
              have hw4 : (848165913/10000000000000:ℝ) ≤ wfun (y + z) := wc_574 (y + z) (by linarith) (by linarith)
              have hw5 : (128184591/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_961 (x + y + z) (by linarith) (by linarith)
              linarith
        · have hw1 : (2090005161/5000000000000:ℝ) ≤ wfun y := wc_382 y (by linarith) (by linarith)
          have hw3 : (1697224391/10000000000000:ℝ) ≤ wfun (x + y) := wc_719 (x + y) (by linarith) (by linarith)
          have hw4 : (1697224391/10000000000000:ℝ) ≤ wfun (y + z) := wc_719 (y + z) (by linarith) (by linarith)
          have hw5 : (18241731/250000000000:ℝ) ≤ wfun (x + y + z) := by
            rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
            · exact le_trans (by norm_num) (wc_924 (x + y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_973 (x + y + z) (by linarith) (by linarith))
          linarith
      · have hw1 : (115281189/5000000000000:ℝ) ≤ wfun y := wc_337 y (by linarith) (by linarith)
        have hw2 : (15429929/1000000000000:ℝ) ≤ wfun z := wc_63 z (by linarith) (by linarith)
        have hw3 : (23815441/10000000000000:ℝ) ≤ wfun (x + y) := wc_487 (x + y) (by linarith) (by linarith)
        have hw4 : (2606310863/10000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (17/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_745 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_756 (y + z) (by linarith) (by linarith))
        have hw5 : (1257182497/10000000000000:ℝ) ≤ wfun (x + y + z) := by
          rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
          · exact le_trans (by norm_num) (wc_962 (x + y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_976 (x + y + z) (by linarith) (by linarith))
        linarith
    · have hw0 : (15429929/1000000000000:ℝ) ≤ wfun x := wc_63 x (by linarith) (by linarith)
      have hw1 : (115281189/5000000000000:ℝ) ≤ wfun y := wc_337 y (by linarith) (by linarith)
      have hw3 : (2606310863/10000000000000:ℝ) ≤ wfun (x + y) := by
        rcases le_total (x + y) (17/4:ℝ) with hq30 | hq30
        · exact le_trans (by norm_num) (wc_745 (x + y) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_756 (x + y) (by linarith) (by linarith))
      have hw4 : (23206737/10000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (17/4:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_488 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_756 (y + z) (by linarith) (by linarith))
      have hw5 : (1257182497/10000000000000:ℝ) ≤ wfun (x + y + z) := by
        rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
        · exact le_trans (by norm_num) (wc_962 (x + y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_978 (x + y + z) (by linarith) (by linarith))
      linarith
  · have hw1 : (11532825879/10000000000000:ℝ) ≤ wfun y := by
      rcases le_total y (13/4:ℝ) with hq10 | hq10
      · exact le_trans (by norm_num) (wc_388 y (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_390 y (by linarith) (by linarith))
    have hw3 : (5787071159/10000000000000:ℝ) ≤ wfun (x + y) := by
      rcases le_total (x + y) (17/4:ℝ) with hq30 | hq30
      · exact le_trans (by norm_num) (wc_753 (x + y) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_759 (x + y) (by linarith) (by linarith))
    have hw4 : (5787071159/10000000000000:ℝ) ≤ wfun (y + z) := by
      rcases le_total (y + z) (17/4:ℝ) with hq40 | hq40
      · exact le_trans (by norm_num) (wc_753 (y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_759 (y + z) (by linarith) (by linarith))
    have hw5 : (3116773877/10000000000000:ℝ) ≤ wfun (x + y + z) := by
      rcases le_total (x + y + z) (21/4:ℝ) with hq50 | hq50
      · exact le_trans (by norm_num) (wc_969 (x + y + z) (by linarith) (by linarith))
      rcases le_total (x + y + z) (11/2:ℝ) with hq51 | hq51
      · exact le_trans (by norm_num) (wc_980 (x + y + z) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_982 (x + y + z) (by linarith) (by linarith))
    linarith

end Zeta23Ext.Bridge.FourPoint
