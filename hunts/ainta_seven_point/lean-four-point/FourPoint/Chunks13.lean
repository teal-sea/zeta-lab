import FourPoint.Cells

/-! Chunk module 13 of 16 of the three-dimensional table.  Each lemma is one
subtree of at most 110 leaves of one box's bisection tree; `FourPoint/Boxes.lean` routes
the box down to them.  Cutting the tree this way gives each subtree its own
heartbeat budget and lets `lake` compile them in parallel. -/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

set_option maxHeartbeats 20000000 in
lemma ch_25 (x y z : ℝ) (hx1 : (1073/1024:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (63/32:ℝ) ≤ y) (hy2 : y ≤ (2021/1024:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (539/512:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (1073/1024:ℝ) with hc | hc
  · rcases le_total x (2151/2048:ℝ) with hc | hc
    · rcases le_total y (4037/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
          have hw5 : (12788137/156250000000:ℝ) ≤ wfun (x + y + z) := wc_560 (x + y + z) (by linarith) (by linarith)
          linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
            have hw5 : (910381357/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_570 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
            have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_577 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw4 : (906687/2000000000000:ℝ) ≤ wfun (y + z) := wc_233 (y + z) (by linarith) (by linarith)
              have hw5 : (227869559/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_569 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_235 (y + z) (by linarith) (by linarith)
              have hw5 : (958721819/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_576 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_238 (x + y) (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
            have hw5 : (191513687/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_577 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw5 : (1007100179/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_579 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw5 : (528304163/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_591 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total y (4037/2048:ℝ) with hc | hc
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
          have hw4 : (128333/125000000000:ℝ) ≤ wfun (y + z) := wc_231 (y + z) (by linarith) (by linarith)
          have hw5 : (56830383/625000000000:ℝ) ≤ wfun (x + y + z) := wc_571 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
          have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
          have hw5 : (1004679561/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_581 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (2141/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_241 (x + y) (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
            have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_580 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_28 z (by linarith) (by linarith)
            have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_251 (x + y) (by linarith) (by linarith)
            have hw4 : (278293/2500000000000:ℝ) ≤ wfun (y + z) := wc_234 (y + z) (by linarith) (by linarith)
            have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_592 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_37 z (by linarith) (by linarith)
            have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_251 (x + y) (by linarith) (by linarith)
            have hw5 : (1157601093/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_604 (x + y + z) (by linarith) (by linarith)
            linarith
  · rcases le_total x (2151/2048:ℝ) with hc | hc
    · rcases le_total y (4037/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw5 : (1005888959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_580 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw5 : (1055337947/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_592 (x + y + z) (by linarith) (by linarith)
            linarith
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
          have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw5 : (553620607/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_595 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw5 : (1158993733/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_603 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total x (4297/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw4 : (29587/250000000000:ℝ) ≤ wfun (y + z) := wc_241 (y + z) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (65990561/1250000000000:ℝ) ≤ wfun x := wc_43 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
              have hw3 : (329/10000000000000:ℝ) ≤ wfun (x + y) := wc_237 (x + y) (by linarith) (by linarith)
              have hw4 : (465149/1000000000000:ℝ) ≤ wfun (y + z) := wc_251 (y + z) (by linarith) (by linarith)
              have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_48 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (41/1250000000000:ℝ) ≤ wfun (x + y) := wc_238 (x + y) (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
            have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_622 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total y (4037/2048:ℝ) with hc | hc
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
          have hw5 : (8629543/78125000000:ℝ) ≤ wfun (x + y + z) := wc_597 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
          have hw1 : (6435510271/10000000000000:ℝ) ≤ wfun y := wc_86 y (by linarith) (by linarith)
          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
          have hw5 : (1208951451/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_610 (x + y + z) (by linarith) (by linarith)
          linarith
      · rcases le_total z (2151/2048:ℝ) with hc | hc
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · rcases le_total y (8079/4096:ℝ) with hc | hc
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (6172561523/10000000000000:ℝ) ≤ wfun y := wc_91 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (1185403/10000000000000:ℝ) ≤ wfun (x + y) := wc_240 (x + y) (by linarith) (by linarith)
              have hw5 : (242372143/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_608 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
              have hw1 : (5909199941/10000000000000:ℝ) ≤ wfun y := wc_93 y (by linarith) (by linarith)
              have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
              have hw3 : (931809/2000000000000:ℝ) ≤ wfun (x + y) := wc_250 (x + y) (by linarith) (by linarith)
              have hw4 : (41/1250000000000:ℝ) ≤ wfun (y + z) := wc_238 (y + z) (by linarith) (by linarith)
              have hw5 : (1265836939/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_621 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (76304221/2000000000000:ℝ) ≤ wfun z := wc_44 z (by linarith) (by linarith)
            have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_251 (x + y) (by linarith) (by linarith)
            have hw5 : (1264316833/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_622 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total x (4307/4096:ℝ) with hc | hc
          · have hw0 : (259133459/10000000000000:ℝ) ≤ wfun x := wc_50 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (29587/250000000000:ℝ) ≤ wfun (x + y) := wc_241 (x + y) (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
            have hw5 : (659665673/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_630 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_52 x (by linarith) (by linarith)
            have hw1 : (5903663357/10000000000000:ℝ) ≤ wfun y := wc_92 y (by linarith) (by linarith)
            have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_51 z (by linarith) (by linarith)
            have hw3 : (465149/1000000000000:ℝ) ≤ wfun (x + y) := wc_251 (x + y) (by linarith) (by linarith)
            have hw4 : (1181561/10000000000000:ℝ) ≤ wfun (y + z) := wc_242 (y + z) (by linarith) (by linarith)
            have hw5 : (275088639/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_640 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_32 (x y z : ℝ) (hx1 : (2141/2048:ℝ) ≤ x) (hx2 : x ≤ (1073/1024:ℝ))
    (hy1 : (2031/1024:ℝ) ≤ y) (hy2 : y ≤ (509/256:ℝ))
    (hz1 : (267/256:ℝ) ≤ z) (hz2 : z ≤ (1073/1024:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total y (4067/2048:ℝ) with hc | hc
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (2809593/500000000000:ℝ) ≤ wfun (x + y) := wc_283 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (1323300249/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_627 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (64456359/10000000000000:ℝ) ≤ wfun (x + y) := wc_289 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (1351302719/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_635 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (690204403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_636 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (176122069/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_641 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (1379579649/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_637 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
              have hw4 : (3594019/1250000000000:ℝ) ≤ wfun (y + z) := wc_268 (y + z) (by linarith) (by linarith)
              have hw5 : (1408130363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_642 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_294 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_294 (x + y) (by linarith) (by linarith)
                have hw4 : (4135373/1000000000000:ℝ) ≤ wfun (y + z) := wc_277 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_296 (x + y) (by linarith) (by linarith)
                have hw4 : (48490713/10000000000000:ℝ) ≤ wfun (y + z) := wc_281 (y + z) (by linarith) (by linarith)
                have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
              have hw4 : (8264047/2000000000000:ℝ) ≤ wfun (y + z) := wc_278 (y + z) (by linarith) (by linarith)
              have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
              linarith
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                have hw5 : (718908779/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_643 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                have hw5 : (1466931139/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_660 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (56237401/10000000000000:ℝ) ≤ wfun (x + y) := wc_282 (x + y) (by linarith) (by linarith)
                have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_291 (y + z) (by linarith) (by linarith)
                have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_295 (y + z) (by linarith) (by linarith)
                have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (64508587/10000000000000:ℝ) ≤ wfun (x + y) := wc_288 (x + y) (by linarith) (by linarith)
                have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_291 (y + z) (by linarith) (by linarith)
                have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_295 (y + z) (by linarith) (by linarith)
                have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_669 (x + y + z) (by linarith) (by linarith)
                linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (73283389/10000000000000:ℝ) ≤ wfun (x + y) := wc_291 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (8129/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                have hw5 : (748158303/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_662 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_294 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                linarith
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_294 (x + y) (by linarith) (by linarith)
                have hw4 : (2809593/500000000000:ℝ) ≤ wfun (y + z) := wc_283 (y + z) (by linarith) (by linarith)
                have hw5 : (305194653/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_667 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
                have hw3 : (92696731/10000000000000:ℝ) ≤ wfun (x + y) := wc_296 (x + y) (by linarith) (by linarith)
                have hw4 : (64456359/10000000000000:ℝ) ≤ wfun (y + z) := wc_289 (y + z) (by linarith) (by linarith)
                have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_669 (x + y + z) (by linarith) (by linarith)
                linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · rcases le_total y (16253/8192:ℝ) with hc | hc
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1954646193/5000000000000:ℝ) ≤ wfun y := wc_117 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (36671379/5000000000000:ℝ) ≤ wfun (x + y) := wc_290 (x + y) (by linarith) (by linarith)
                have hw4 : (73283389/10000000000000:ℝ) ≤ wfun (y + z) := wc_291 (y + z) (by linarith) (by linarith)
                have hw5 : (77795021/500000000000:ℝ) ≤ wfun (x + y + z) := wc_669 (x + y + z) (by linarith) (by linarith)
                linarith
              · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
                have hw1 : (1902333181/5000000000000:ℝ) ≤ wfun y := wc_121 y (by linarith) (by linarith)
                have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
                have hw3 : (20684771/2500000000000:ℝ) ≤ wfun (x + y) := wc_294 (x + y) (by linarith) (by linarith)
                have hw4 : (82672123/10000000000000:ℝ) ≤ wfun (y + z) := wc_295 (y + z) (by linarith) (by linarith)
                have hw5 : (793048687/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_677 (x + y + z) (by linarith) (by linarith)
                linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (3803388551/10000000000000:ℝ) ≤ wfun y := wc_118 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (82672123/10000000000000:ℝ) ≤ wfun (x + y) := wc_295 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (359863857/1000000000000:ℝ) ≤ wfun y := wc_122 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
              linarith
  · rcases le_total z (2141/2048:ℝ) with hc | hc
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (718477089/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_644 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (1466050409/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_661 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
            have hw5 : (747260403/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_664 (x + y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_314 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_317 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
              linarith
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_314 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (1495418369/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_663 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_317 (x + y) (by linarith) (by linarith)
              have hw4 : (11229273/2000000000000:ℝ) ≤ wfun (y + z) := wc_284 (y + z) (by linarith) (by linarith)
              have hw5 : (1525057363/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_668 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_314 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_317 (x + y) (by linarith) (by linarith)
              have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
              have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4277/4096:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (135743827/1000000000000:ℝ) ≤ wfun z := wc_27 z (by linarith) (by linarith)
            have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
            have hw4 : (73224081/10000000000000:ℝ) ≤ wfun (y + z) := wc_292 (y + z) (by linarith) (by linarith)
            have hw5 : (1554033673/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_671 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (139137559/1250000000000:ℝ) ≤ wfun z := wc_33 z (by linarith) (by linarith)
            have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
            have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
            have hw5 : (807312237/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_680 (x + y + z) (by linarith) (by linarith)
            linarith
    · rcases le_total x (4287/4096:ℝ) with hc | hc
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (194370837/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_670 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (1585145671/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_678 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (46310863/5000000000000:ℝ) ≤ wfun (x + y) := wc_297 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (25782839/2500000000000:ℝ) ≤ wfun (x + y) := wc_313 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8569/8192:ℝ) with hc | hc
            · have hw0 : (1000229897/10000000000000:ℝ) ≤ wfun x := wc_35 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_314 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_38 x (by linarith) (by linarith)
              have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_317 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
              linarith
          · have hw0 : (446763507/5000000000000:ℝ) ≤ wfun x := wc_36 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (57053907/5000000000000:ℝ) ≤ wfun (x + y) := wc_315 (x + y) (by linarith) (by linarith)
            have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
            have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
            linarith
      · rcases le_total y (8139/4096:ℝ) with hc | hc
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_314 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (100974599/625000000000:ℝ) ≤ wfun (x + y + z) := wc_679 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_317 (x + y) (by linarith) (by linarith)
              have hw4 : (46273399/5000000000000:ℝ) ≤ wfun (y + z) := wc_298 (y + z) (by linarith) (by linarith)
              have hw5 : (51447179/312500000000:ℝ) ≤ wfun (x + y + z) := wc_683 (x + y + z) (by linarith) (by linarith)
              linarith
          · rcases le_total x (8579/8192:ℝ) with hc | hc
            · have hw0 : (396484213/5000000000000:ℝ) ≤ wfun x := wc_39 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (114200161/10000000000000:ℝ) ≤ wfun (x + y) := wc_314 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (335458679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_684 (x + y + z) (by linarith) (by linarith)
              linarith
            · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_41 x (by linarith) (by linarith)
              have hw1 : (339970037/1000000000000:ℝ) ≤ wfun y := wc_123 y (by linarith) (by linarith)
              have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
              have hw3 : (15728411/1250000000000:ℝ) ≤ wfun (x + y) := wc_317 (x + y) (by linarith) (by linarith)
              have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
              have hw5 : (1708543871/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_694 (x + y + z) (by linarith) (by linarith)
              linarith
        · rcases le_total z (4287/4096:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (446763507/5000000000000:ℝ) ≤ wfun z := wc_36 z (by linarith) (by linarith)
            have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
            have hw4 : (57053907/5000000000000:ℝ) ≤ wfun (y + z) := wc_315 (y + z) (by linarith) (by linarith)
            have hw5 : (838143789/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_685 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_40 x (by linarith) (by linarith)
            have hw1 : (3206563771/10000000000000:ℝ) ≤ wfun y := wc_125 y (by linarith) (by linarith)
            have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_40 z (by linarith) (by linarith)
            have hw3 : (17237539/1250000000000:ℝ) ≤ wfun (x + y) := wc_318 (x + y) (by linarith) (by linarith)
            have hw4 : (17237539/1250000000000:ℝ) ≤ wfun (y + z) := wc_318 (y + z) (by linarith) (by linarith)
            have hw5 : (1739017297/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_696 (x + y + z) (by linarith) (by linarith)
            linarith

set_option maxHeartbeats 20000000 in
lemma ch_44 (x y z : ℝ) (hx1 : (267/256:ℝ) ≤ x) (hx2 : x ≤ (539/512:ℝ))
    (hy1 : (509/256:ℝ) ≤ y) (hy2 : y ≤ (1023/512:ℝ))
    (hz1 : (539/512:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
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
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
            have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
            have hw3 : (92247841/10000000000000:ℝ) ≤ wfun (x + y) := wc_300 (x + y) (by linarith) (by linarith)
            have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_341 (y + z) (by linarith) (by linarith)
            have hw5 : (1922008203/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_711 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (139137559/1250000000000:ℝ) ≤ wfun x := wc_28 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
            have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
            have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
            have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_723 (x + y + z) (by linarith) (by linarith)
            linarith
        · rcases le_total y (4077/2048:ℝ) with hc | hc
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (2836262683/10000000000000:ℝ) ≤ wfun y := wc_127 y (by linarith) (by linarith)
            have hw3 : (13745521/1000000000000:ℝ) ≤ wfun (x + y) := wc_320 (x + y) (by linarith) (by linarith)
            have hw4 : (325017537/10000000000000:ℝ) ≤ wfun (y + z) := wc_341 (y + z) (by linarith) (by linarith)
            have hw5 : (2056124169/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_723 (x + y + z) (by linarith) (by linarith)
            linarith
          · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_37 x (by linarith) (by linarith)
            have hw1 : (1245418929/5000000000000:ℝ) ≤ wfun y := wc_133 y (by linarith) (by linarith)
            have hw3 : (23941523/1250000000000:ℝ) ≤ wfun (x + y) := wc_326 (x + y) (by linarith) (by linarith)
            have hw4 : (405098789/10000000000000:ℝ) ≤ wfun (y + z) := wc_347 (y + z) (by linarith) (by linarith)
            have hw5 : (2194341861/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_726 (x + y + z) (by linarith) (by linarith)
            linarith
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
        have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
        have hw3 : (11456693/1250000000000:ℝ) ≤ wfun (x + y) := wc_302 (x + y) (by linarith) (by linarith)
        have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
        have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
        linarith
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
        have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
        have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
        have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
        have hw5 : (272985599/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_728 (x + y + z) (by linarith) (by linarith)
        linarith
      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
        have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
        have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
        have hw4 : (694482783/10000000000000:ℝ) ≤ wfun (y + z) := wc_354 (y + z) (by linarith) (by linarith)
        have hw5 : (3861047/15625000000:ℝ) ≤ wfun (x + y + z) := wc_733 (x + y + z) (by linarith) (by linarith)
        linarith
  · rcases le_total y (2041/1024:ℝ) with hc | hc
    · rcases le_total z (1083/1024:ℝ) with hc | hc
      · rcases le_total x (2151/2048:ℝ) with hc | hc
        · have hw0 : (76304221/2000000000000:ℝ) ≤ wfun x := wc_44 x (by linarith) (by linarith)
          have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
          have hw3 : (7636599/400000000000:ℝ) ≤ wfun (x + y) := wc_327 (x + y) (by linarith) (by linarith)
          have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
          have hw5 : (2189105517/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_727 (x + y + z) (by linarith) (by linarith)
          linarith
        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_51 x (by linarith) (by linarith)
          have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
          have hw3 : (63400731/2500000000000:ℝ) ≤ wfun (x + y) := wc_335 (x + y) (by linarith) (by linarith)
          have hw4 : (161986357/5000000000000:ℝ) ≤ wfun (y + z) := wc_342 (y + z) (by linarith) (by linarith)
          have hw5 : (291380049/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_732 (x + y + z) (by linarith) (by linarith)
          linarith
      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
        have hw1 : (248869577/1000000000000:ℝ) ≤ wfun y := wc_128 y (by linarith) (by linarith)
        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
        have hw3 : (190300253/10000000000000:ℝ) ≤ wfun (x + y) := wc_328 (x + y) (by linarith) (by linarith)
        have hw4 : (24610003/500000000000:ℝ) ≤ wfun (y + z) := wc_350 (y + z) (by linarith) (by linarith)
        have hw5 : (3861047/15625000000:ℝ) ≤ wfun (x + y + z) := wc_733 (x + y + z) (by linarith) (by linarith)
        linarith
    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
      have hw1 : (1867963109/10000000000000:ℝ) ≤ wfun y := wc_136 y (by linarith) (by linarith)
      have hw3 : (161986357/5000000000000:ℝ) ≤ wfun (x + y) := wc_342 (x + y) (by linarith) (by linarith)
      have hw4 : (489049523/10000000000000:ℝ) ≤ wfun (y + z) := wc_351 (y + z) (by linarith) (by linarith)
      have hw5 : (1229661173/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_734 (x + y + z) (by linarith) (by linarith)
      linarith

set_option maxHeartbeats 20000000 in
lemma ch_60 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (73/64:ℝ))
    (hy1 : (121/64:ℝ) ≤ y) (hy2 : y ≤ (141/64:ℝ))
    (hz1 : (179/64:ℝ) ≤ z) (hz2 : z ≤ (105/32:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total z (389/128:ℝ) with hc | hc
  · rcases le_total y (131/64:ℝ) with hc | hc
    · rcases le_total z (747/256:ℝ) with hc | hc
      · have hw2 : (1457053011/2000000000000:ℝ) ≤ wfun z := wc_187 z (by linarith) (by linarith)
        have hw4 : (498772193/10000000000000:ℝ) ≤ wfun (y + z) := by
          rcases le_total (y + z) (19/4:ℝ) with hq40 | hq40
          · exact le_trans (by norm_num) (wc_761 (y + z) (by linarith) (by linarith))
          exact le_trans (by norm_num) (wc_762 (y + z) (by linarith) (by linarith))
        linarith
      · linarith
    · linarith
  · linarith

set_option maxHeartbeats 20000000 in
lemma ch_62 (x y z : ℝ) (hx1 : (63/64:ℝ) ≤ x) (hx2 : x ≤ (17/16:ℝ))
    (hy1 : (747/256:ℝ) ≤ y) (hy2 : y ≤ (1525/512:ℝ))
    (hz1 : (63/64:ℝ) ≤ z) (hz2 : z ≤ (17/16:ℝ)) :
    (2310/1000000:ℝ) ≤ (1/(2500:ℝ)) * (x + y + z) + 2/3 * wfun x + 2/3 * wfun y + 2/3 * wfun z + wfun (x + y) + wfun (y + z) + 2 * wfun (x + y + z) := by
  have hn0 := wfun_nonneg x
  have hn1 := wfun_nonneg y
  have hn2 := wfun_nonneg z
  have hn3 := wfun_nonneg (x + y)
  have hn4 := wfun_nonneg (y + z)
  have hn5 := wfun_nonneg (x + y + z)
  rcases le_total x (131/128:ℝ) with hc | hc
  · have hw0 : (2370342229/2500000000000:ℝ) ≤ wfun x := by
      rcases le_total x (1:ℝ) with hq00 | hq00
      · exact le_trans (by norm_num) (wc_5 x (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_7 x (by linarith) (by linarith))
    have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
    have hw3 : (76620491/10000000000000:ℝ) ≤ wfun (x + y) := by
      rcases le_total (x + y) (4:ℝ) with hq30 | hq30
      · exact le_trans (by norm_num) (wc_404 (x + y) (by linarith) (by linarith))
      exact le_trans (by norm_num) (wc_433 (x + y) (by linarith) (by linarith))
    linarith
  · rcases le_total z (131/128:ℝ) with hc | hc
    · have hw1 : (261299809/2000000000000:ℝ) ≤ wfun y := wc_192 y (by linarith) (by linarith)
      have hw2 : (2370342229/2500000000000:ℝ) ≤ wfun z := by
        rcases le_total z (1:ℝ) with hq20 | hq20
        · exact le_trans (by norm_num) (wc_5 z (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_7 z (by linarith) (by linarith))
      have hw4 : (76620491/10000000000000:ℝ) ≤ wfun (y + z) := by
        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
        · exact le_trans (by norm_num) (wc_404 (y + z) (by linarith) (by linarith))
        exact le_trans (by norm_num) (wc_433 (y + z) (by linarith) (by linarith))
      linarith
    · rcases le_total y (3019/1024:ℝ) with hc | hc
      · rcases le_total x (267/256:ℝ) with hc | hc
        · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
          have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
          have hw3 : (122092393/5000000000000:ℝ) ≤ wfun (x + y) := wc_407 (x + y) (by linarith) (by linarith)
          have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
            rcases le_total (y + z) (4:ℝ) with hq40 | hq40
            · exact le_trans (by norm_num) (wc_408 (y + z) (by linarith) (by linarith))
            exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
          linarith
        · rcases le_total z (267/256:ℝ) with hc | hc
          · have hw1 : (100676353/250000000000:ℝ) ≤ wfun y := wc_191 y (by linarith) (by linarith)
            have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
            have hw3 : (436723/500000000000:ℝ) ≤ wfun (x + y) := by
              rcases le_total (x + y) (4:ℝ) with hq30 | hq30
              · exact le_trans (by norm_num) (wc_412 (x + y) (by linarith) (by linarith))
              exact le_trans (by norm_num) (wc_439 (x + y) (by linarith) (by linarith))
            have hw4 : (122092393/5000000000000:ℝ) ≤ wfun (y + z) := wc_407 (y + z) (by linarith) (by linarith)
            linarith
          · rcases le_total y (6007/2048:ℝ) with hc | hc
            · have hw1 : (2995265257/5000000000000:ℝ) ≤ wfun y := wc_190 y (by linarith) (by linarith)
              have hw3 : (82600037/5000000000000:ℝ) ≤ wfun (x + y) := wc_411 (x + y) (by linarith) (by linarith)
              have hw4 : (82600037/5000000000000:ℝ) ≤ wfun (y + z) := wc_411 (y + z) (by linarith) (by linarith)
              linarith
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (539/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (816631931/2000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (11042139/1250000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_417 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (x + y) (by linarith) (by linarith))
                  have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_417 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                  have hw5 : (194973/156250000000:ℝ) ≤ wfun (x + y + z) := wc_766 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (816631931/2000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw3 : (11042139/1250000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_417 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (x + y) (by linarith) (by linarith))
                  have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_423 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
                  have hw5 : (9159361/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_784 (x + y + z) (by linarith) (by linarith)
                  linarith
              · rcases le_total z (539/512:ℝ) with hc | hc
                · have hw1 : (816631931/2000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                  have hw3 : (436723/500000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_423 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_439 (x + y) (by linarith) (by linarith))
                  have hw4 : (11042139/1250000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_417 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_432 (y + z) (by linarith) (by linarith))
                  have hw5 : (9159361/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_784 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (816631931/2000000000000:ℝ) ≤ wfun y := wc_193 y (by linarith) (by linarith)
                  have hw3 : (436723/500000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_423 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_439 (x + y) (by linarith) (by linarith))
                  have hw4 : (436723/500000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_423 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_439 (y + z) (by linarith) (by linarith))
                  have hw5 : (91940011/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_800 (x + y + z) (by linarith) (by linarith)
                  linarith
      · rcases le_total x (267/256:ℝ) with hc | hc
        · rcases le_total z (267/256:ℝ) with hc | hc
          · rcases le_total y (6069/2048:ℝ) with hc | hc
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
              have hw3 : (34242453/10000000000000:ℝ) ≤ wfun (x + y) := by
                rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                · exact le_trans (by norm_num) (wc_416 (x + y) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_436 (x + y) (by linarith) (by linarith))
              have hw4 : (34242453/10000000000000:ℝ) ≤ wfun (y + z) := by
                rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                · exact le_trans (by norm_num) (wc_416 (y + z) (by linarith) (by linarith))
                exact le_trans (by norm_num) (wc_436 (y + z) (by linarith) (by linarith))
              linarith
            · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_13 x (by linarith) (by linarith)
              have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
              have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_13 z (by linarith) (by linarith)
              linarith
          · rcases le_total y (6069/2048:ℝ) with hc | hc
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                have hw3 : (30026951/2000000000000:ℝ) ≤ wfun (x + y) := wc_415 (x + y) (by linarith) (by linarith)
                have hw5 : (790561/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_764 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12107/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                    have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (23464061/2000000000000:ℝ) ≤ wfun (x + y) := wc_421 (x + y) (by linarith) (by linarith)
                    have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_437 (y + z) (by linarith) (by linarith))
                    have hw5 : (7987727/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_778 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                    have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                    have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                    have hw3 : (34242453/10000000000000:ℝ) ≤ wfun (x + y) := by
                      rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                      · exact le_trans (by norm_num) (wc_427 (x + y) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_436 (x + y) (by linarith) (by linarith))
                    have hw5 : (208853/20000000000:ℝ) ≤ wfun (x + y + z) := wc_792 (x + y + z) (by linarith) (by linarith)
                    linarith
                · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                  have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                  have hw3 : (34242453/10000000000000:ℝ) ≤ wfun (x + y) := by
                    rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                    · exact le_trans (by norm_num) (wc_422 (x + y) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_436 (x + y) (by linarith) (by linarith))
                  have hw5 : (128003319/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_796 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (529/512:ℝ) with hc | hc
              · have hw0 : (1175437333/2500000000000:ℝ) ≤ wfun x := wc_12 x (by linarith) (by linarith)
                have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                have hw3 : (2673983/5000000000000:ℝ) ≤ wfun (x + y) := by
                  rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                  · exact le_trans (by norm_num) (wc_426 (x + y) (by linarith) (by linarith))
                  exact le_trans (by norm_num) (wc_441 (x + y) (by linarith) (by linarith))
                have hw5 : (81477507/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_791 (x + y + z) (by linarith) (by linarith)
                linarith
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12169/4096:ℝ) with hc | hc
                  · rcases le_total x (1063/1024:ℝ) with hc | hc
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                      have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (8327617/5000000000000:ℝ) ≤ wfun (x + y) := by
                        rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                        · exact le_trans (by norm_num) (wc_430 (x + y) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_438 (x + y) (by linarith) (by linarith))
                      have hw5 : (99799521/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_815 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                      have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (752127/10000000000000:ℝ) ≤ wfun (x + y) := wc_446 (x + y) (by linarith) (by linarith)
                      have hw5 : (138225741/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_831 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (1063/1024:ℝ) with hc | hc
                    · have hw0 : (2957142633/10000000000000:ℝ) ≤ wfun x := wc_16 x (by linarith) (by linarith)
                      have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw5 : (10122207/312500000000:ℝ) ≤ wfun (x + y + z) := wc_838 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_21 x (by linarith) (by linarith)
                      have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw5 : (209768083/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (12169/4096:ℝ) with hc | hc
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                    have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                    have hw3 : (752127/10000000000000:ℝ) ≤ wfun (x + y) := by
                      rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                      · exact le_trans (by norm_num) (wc_430 (x + y) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_442 (x + y) (by linarith) (by linarith))
                    have hw4 : (163329/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                    have hw5 : (364051049/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_849 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (1626727581/10000000000000:ℝ) ≤ wfun x := wc_17 x (by linarith) (by linarith)
                    have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                    have hw4 : (7532357/2500000000000:ℝ) ≤ wfun (y + z) := wc_490 (y + z) (by linarith) (by linarith)
                    have hw5 : (13126113/250000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
                    linarith
        · rcases le_total z (267/256:ℝ) with hc | hc
          · rcases le_total y (6069/2048:ℝ) with hc | hc
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw4 : (30026951/2000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (796707/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_763 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (12107/4096:ℝ) with hc | hc
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                    have hw3 : (9692591/5000000000000:ℝ) ≤ wfun (x + y) := by
                      rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                      · exact le_trans (by norm_num) (wc_428 (x + y) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_437 (x + y) (by linarith) (by linarith))
                    have hw4 : (23464061/2000000000000:ℝ) ≤ wfun (y + z) := wc_421 (y + z) (by linarith) (by linarith)
                    have hw5 : (7987727/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_778 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                    have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                    have hw4 : (34242453/10000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_427 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_436 (y + z) (by linarith) (by linarith))
                    have hw5 : (208853/20000000000:ℝ) ≤ wfun (x + y + z) := wc_792 (x + y + z) (by linarith) (by linarith)
                    linarith
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw4 : (30026951/2000000000000:ℝ) ≤ wfun (y + z) := wc_415 (y + z) (by linarith) (by linarith)
                  have hw5 : (39699707/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_779 (x + y + z) (by linarith) (by linarith)
                  linarith
                · have hw1 : (2539642107/10000000000000:ℝ) ≤ wfun y := wc_195 y (by linarith) (by linarith)
                  have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                  have hw4 : (34242453/10000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_422 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_436 (y + z) (by linarith) (by linarith))
                  have hw5 : (128003319/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_796 (x + y + z) (by linarith) (by linarith)
                  linarith
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_30 x (by linarith) (by linarith)
                  have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw4 : (2673983/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_426 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_441 (y + z) (by linarith) (by linarith))
                  have hw5 : (82109019/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_790 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (12169/4096:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                      have hw4 : (752127/10000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_430 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_442 (y + z) (by linarith) (by linarith))
                      have hw5 : (99799521/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_815 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                      have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                      have hw4 : (752127/10000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_430 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_442 (y + z) (by linarith) (by linarith))
                      have hw5 : (138225741/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_831 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                      have hw5 : (10122207/312500000000:ℝ) ≤ wfun (x + y + z) := wc_838 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                      have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                      have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                      have hw3 : (1350713/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                      have hw5 : (209768083/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_857 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total z (529/512:ℝ) with hc | hc
                · have hw1 : (1362675081/10000000000000:ℝ) ≤ wfun y := wc_204 y (by linarith) (by linarith)
                  have hw2 : (1175437333/2500000000000:ℝ) ≤ wfun z := wc_12 z (by linarith) (by linarith)
                  have hw3 : (32421/1000000000000:ℝ) ≤ wfun (x + y) := wc_464 (x + y) (by linarith) (by linarith)
                  have hw4 : (2673983/5000000000000:ℝ) ≤ wfun (y + z) := by
                    rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                    · exact le_trans (by norm_num) (wc_426 (y + z) (by linarith) (by linarith))
                    exact le_trans (by norm_num) (wc_441 (y + z) (by linarith) (by linarith))
                  have hw5 : (19764329/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_816 (x + y + z) (by linarith) (by linarith)
                  linarith
                · rcases le_total y (12169/4096:ℝ) with hc | hc
                  · have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                    have hw3 : (163329/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                    have hw4 : (752127/10000000000000:ℝ) ≤ wfun (y + z) := by
                      rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                      · exact le_trans (by norm_num) (wc_430 (y + z) (by linarith) (by linarith))
                      exact le_trans (by norm_num) (wc_442 (y + z) (by linarith) (by linarith))
                    have hw5 : (364051049/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_849 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                    have hw2 : (1626727581/10000000000000:ℝ) ≤ wfun z := wc_17 z (by linarith) (by linarith)
                    have hw3 : (7532357/2500000000000:ℝ) ≤ wfun (x + y) := wc_490 (x + y) (by linarith) (by linarith)
                    have hw5 : (13126113/250000000000:ℝ) ≤ wfun (x + y + z) := wc_874 (x + y + z) (by linarith) (by linarith)
                    linarith
          · rcases le_total y (6069/2048:ℝ) with hc | hc
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12107/4096:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (29065073/5000000000000:ℝ) ≤ wfun (x + y) := by
                        rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                        · exact le_trans (by norm_num) (wc_428 (x + y) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_434 (x + y) (by linarith) (by linarith))
                      have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_437 (y + z) (by linarith) (by linarith))
                      have hw5 : (64635657/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_795 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                        have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw3 : (9692591/5000000000000:ℝ) ≤ wfun (x + y) := by
                          rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                          · exact le_trans (by norm_num) (wc_429 (x + y) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_437 (x + y) (by linarith) (by linarith))
                        have hw4 : (29065073/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_434 (y + z) (by linarith) (by linarith))
                        have hw5 : (48333597/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_804 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                        have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                        have hw3 : (9692591/5000000000000:ℝ) ≤ wfun (x + y) := by
                          rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                          · exact le_trans (by norm_num) (wc_429 (x + y) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_437 (x + y) (by linarith) (by linarith))
                        have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_437 (y + z) (by linarith) (by linarith))
                        have hw5 : (269255433/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_827 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                        have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw3 : (6937709/10000000000000:ℝ) ≤ wfun (x + y) := by
                          rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                          · exact le_trans (by norm_num) (wc_431 (x + y) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_440 (x + y) (by linarith) (by linarith))
                        have hw4 : (6937709/10000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_431 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_440 (y + z) (by linarith) (by linarith))
                        have hw5 : (116785217/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_820 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                        have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                        have hw3 : (6937709/10000000000000:ℝ) ≤ wfun (x + y) := by
                          rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                          · exact le_trans (by norm_num) (wc_431 (x + y) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_440 (x + y) (by linarith) (by linarith))
                        have hw5 : (79057119/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_836 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                        have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw4 : (6937709/10000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_431 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_440 (y + z) (by linarith) (by linarith))
                        have hw5 : (79057119/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_836 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total y (24245/8192:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw3 : (730337/2000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                          have hw4 : (730337/2000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                          have hw5 : (51531267/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_854 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw5 : (494198099/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_868 (x + y + z) (by linarith) (by linarith)
                          linarith
                · rcases le_total y (12107/4096:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                      have hw3 : (29065073/5000000000000:ℝ) ≤ wfun (x + y) := by
                        rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                        · exact le_trans (by norm_num) (wc_428 (x + y) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_434 (x + y) (by linarith) (by linarith))
                      have hw5 : (268216841/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_829 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                      have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                      have hw3 : (9692591/5000000000000:ℝ) ≤ wfun (x + y) := by
                        rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                        · exact le_trans (by norm_num) (wc_429 (x + y) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_437 (x + y) (by linarith) (by linarith))
                      have hw5 : (356014641/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_843 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                      have hw3 : (6937709/10000000000000:ℝ) ≤ wfun (x + y) := by
                        rcases le_total (x + y) (4:ℝ) with hq30 | hq30
                        · exact le_trans (by norm_num) (wc_431 (x + y) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_440 (x + y) (by linarith) (by linarith))
                      have hw5 : (409434977/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_856 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (1083/1024:ℝ) with hc | hc
                      · rcases le_total y (24245/8192:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                          have hw3 : (730337/2000000000000:ℝ) ≤ wfun (x + y) := wc_447 (x + y) (by linarith) (by linarith)
                          have hw5 : (519328881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                          have hw5 : (15261593/250000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                        have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                        have hw5 : (318168869/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                        linarith
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12107/4096:ℝ) with hc | hc
                  · rcases le_total x (1083/1024:ℝ) with hc | hc
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw3 : (70603/500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                        have hw4 : (29065073/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_434 (y + z) (by linarith) (by linarith))
                        have hw5 : (269255433/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_827 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                        have hw3 : (70603/500000000000:ℝ) ≤ wfun (x + y) := wc_445 (x + y) (by linarith) (by linarith)
                        have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_429 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_437 (y + z) (by linarith) (by linarith))
                        have hw5 : (89347967/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_841 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                      have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw4 : (9692591/5000000000000:ℝ) ≤ wfun (y + z) := by
                        rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                        · exact le_trans (by norm_num) (wc_428 (y + z) (by linarith) (by linarith))
                        exact le_trans (by norm_num) (wc_437 (y + z) (by linarith) (by linarith))
                      have hw5 : (356014641/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_843 (x + y + z) (by linarith) (by linarith)
                      linarith
                  · rcases le_total x (1083/1024:ℝ) with hc | hc
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw4 : (6937709/10000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_431 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_440 (y + z) (by linarith) (by linarith))
                        have hw5 : (82203603/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_855 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total y (24245/8192:ℝ) with hc | hc
                        · have hw1 : (2917054281/10000000000000:ℝ) ≤ wfun y := wc_199 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw4 : (730337/2000000000000:ℝ) ≤ wfun (y + z) := wc_447 (y + z) (by linarith) (by linarith)
                          have hw5 : (519328881/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_871 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw1 : (2561735901/10000000000000:ℝ) ≤ wfun y := wc_201 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw5 : (15261593/250000000000:ℝ) ≤ wfun (x + y + z) := wc_894 (x + y + z) (by linarith) (by linarith)
                          linarith
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                        have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw4 : (6937709/10000000000000:ℝ) ≤ wfun (y + z) := by
                          rcases le_total (y + z) (4:ℝ) with hq40 | hq40
                          · exact le_trans (by norm_num) (wc_431 (y + z) (by linarith) (by linarith))
                          exact le_trans (by norm_num) (wc_440 (y + z) (by linarith) (by linarith))
                        have hw5 : (32361139/625000000000:ℝ) ≤ wfun (x + y + z) := wc_872 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                        have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                        have hw5 : (318168869/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_896 (x + y + z) (by linarith) (by linarith)
                        linarith
                · rcases le_total y (12107/4096:ℝ) with hc | hc
                  · have hw1 : (3285883949/10000000000000:ℝ) ≤ wfun y := wc_194 y (by linarith) (by linarith)
                    have hw5 : (227036969/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_862 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (319327517/1250000000000:ℝ) ≤ wfun y := wc_200 y (by linarith) (by linarith)
                    have hw5 : (63145721/1000000000000:ℝ) ≤ wfun (x + y + z) := wc_897 (x + y + z) (by linarith) (by linarith)
                    linarith
            · rcases le_total x (539/512:ℝ) with hc | hc
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12169/4096:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                        have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw5 : (183435743/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_848 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total y (24307/8192:ℝ) with hc | hc
                        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                          have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw3 : (5269/2500000000000:ℝ) ≤ wfun (x + y) := wc_448 (x + y) (by linarith) (by linarith)
                          have hw5 : (23483423/500000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                          have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw5 : (69585763/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_875 (x + y + z) (by linarith) (by linarith)
                          linarith
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · rcases le_total y (24307/8192:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                          have hw4 : (5269/2500000000000:ℝ) ≤ wfun (y + z) := wc_448 (y + z) (by linarith) (by linarith)
                          have hw5 : (23483423/500000000000:ℝ) ≤ wfun (x + y + z) := wc_865 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
                          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                          have hw5 : (69585763/1250000000000:ℝ) ≤ wfun (x + y + z) := wc_875 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (24307/8192:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw5 : (11665557/200000000000:ℝ) ≤ wfun (x + y + z) := wc_886 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw5 : (5435249/80000000000:ℝ) ≤ wfun (x + y + z) := wc_900 (x + y + z) (by linarith) (by linarith)
                          linarith
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                        have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw5 : (529106123/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_873 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total y (24369/8192:ℝ) with hc | hc
                        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                          have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw4 : (21693/40000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                          have hw5 : (650776829/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_898 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                          have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw3 : (1298021/5000000000000:ℝ) ≤ wfun (x + y) := wc_468 (x + y) (by linarith) (by linarith)
                          have hw4 : (11506103/5000000000000:ℝ) ≤ wfun (y + z) := wc_484 (y + z) (by linarith) (by linarith)
                          have hw5 : (751854739/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                          linarith
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · rcases le_total y (24369/8192:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                          have hw3 : (21693/40000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                          have hw5 : (650776829/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_898 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                          have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                          have hw3 : (11506103/5000000000000:ℝ) ≤ wfun (x + y) := wc_484 (x + y) (by linarith) (by linarith)
                          have hw4 : (1298021/5000000000000:ℝ) ≤ wfun (y + z) := wc_468 (y + z) (by linarith) (by linarith)
                          have hw5 : (751854739/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_914 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · rcases le_total y (24369/8192:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (1635115293/10000000000000:ℝ) ≤ wfun y := wc_206 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw3 : (21693/40000000000:ℝ) ≤ wfun (x + y) := wc_470 (x + y) (by linarith) (by linarith)
                          have hw4 : (21693/40000000000:ℝ) ≤ wfun (y + z) := wc_470 (y + z) (by linarith) (by linarith)
                          have hw5 : (782495959/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_915 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (686336349/5000000000000:ℝ) ≤ wfun y := wc_209 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw3 : (11506103/5000000000000:ℝ) ≤ wfun (x + y) := wc_484 (x + y) (by linarith) (by linarith)
                          have hw4 : (11506103/5000000000000:ℝ) ≤ wfun (y + z) := wc_484 (y + z) (by linarith) (by linarith)
                          have hw5 : (55778547/625000000000:ℝ) ≤ wfun (x + y + z) := wc_932 (x + y + z) (by linarith) (by linarith)
                          linarith
                · rcases le_total y (12169/4096:ℝ) with hc | hc
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                      have hw4 : (163329/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                      have hw5 : (144825181/2500000000000:ℝ) ≤ wfun (x + y + z) := wc_888 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · rcases le_total z (1083/1024:ℝ) with hc | hc
                      · rcases le_total y (24307/8192:ℝ) with hc | hc
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                          have hw4 : (32949/1000000000000:ℝ) ≤ wfun (y + z) := wc_461 (y + z) (by linarith) (by linarith)
                          have hw5 : (354311107/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                          have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
                          have hw4 : (2319419/2500000000000:ℝ) ≤ wfun (y + z) := wc_474 (y + z) (by linarith) (by linarith)
                          have hw5 : (50857271/625000000000:ℝ) ≤ wfun (x + y + z) := wc_918 (x + y + z) (by linarith) (by linarith)
                          linarith
                      · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                        have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                        have hw2 : (433353/5000000000000:ℝ) ≤ wfun z := wc_57 z (by linarith) (by linarith)
                        have hw4 : (3526053/2500000000000:ℝ) ≤ wfun (y + z) := wc_478 (y + z) (by linarith) (by linarith)
                        have hw5 : (168599037/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_925 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total x (1073/1024:ℝ) with hc | hc
                    · have hw0 : (349265369/5000000000000:ℝ) ≤ wfun x := wc_29 x (by linarith) (by linarith)
                      have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                      have hw4 : (7532357/2500000000000:ℝ) ≤ wfun (y + z) := wc_490 (y + z) (by linarith) (by linarith)
                      have hw5 : (155433679/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_917 (x + y + z) (by linarith) (by linarith)
                      linarith
                    · have hw0 : (160574441/10000000000000:ℝ) ≤ wfun x := wc_45 x (by linarith) (by linarith)
                      have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                      have hw3 : (1350713/2500000000000:ℝ) ≤ wfun (x + y) := wc_471 (x + y) (by linarith) (by linarith)
                      have hw4 : (7532357/2500000000000:ℝ) ≤ wfun (y + z) := wc_490 (y + z) (by linarith) (by linarith)
                      have hw5 : (459679121/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                      linarith
              · rcases le_total z (539/512:ℝ) with hc | hc
                · rcases le_total y (12169/4096:ℝ) with hc | hc
                  · rcases le_total x (1083/1024:ℝ) with hc | hc
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw3 : (1313/40000000000:ℝ) ≤ wfun (x + y) := wc_462 (x + y) (by linarith) (by linarith)
                        have hw5 : (581537173/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_887 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · rcases le_total y (24307/8192:ℝ) with hc | hc
                        · have hw1 : (2229636307/10000000000000:ℝ) ≤ wfun y := wc_202 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw3 : (32949/1000000000000:ℝ) ≤ wfun (x + y) := wc_461 (x + y) (by linarith) (by linarith)
                          have hw5 : (354311107/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_906 (x + y + z) (by linarith) (by linarith)
                          linarith
                        · have hw1 : (240095521/1250000000000:ℝ) ≤ wfun y := wc_205 y (by linarith) (by linarith)
                          have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                          have hw3 : (2319419/2500000000000:ℝ) ≤ wfun (x + y) := wc_474 (x + y) (by linarith) (by linarith)
                          have hw5 : (50857271/625000000000:ℝ) ≤ wfun (x + y + z) := wc_918 (x + y + z) (by linarith) (by linarith)
                          linarith
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                        have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw3 : (3526053/2500000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
                        have hw5 : (706509509/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_907 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                        have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                        have hw3 : (3526053/2500000000000:ℝ) ≤ wfun (x + y) := wc_478 (x + y) (by linarith) (by linarith)
                        have hw5 : (168599037/2000000000000:ℝ) ≤ wfun (x + y + z) := wc_925 (x + y + z) (by linarith) (by linarith)
                        linarith
                  · rcases le_total x (1083/1024:ℝ) with hc | hc
                    · rcases le_total z (1073/1024:ℝ) with hc | hc
                      · have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                        have hw2 : (349265369/5000000000000:ℝ) ≤ wfun z := wc_29 z (by linarith) (by linarith)
                        have hw3 : (30275949/10000000000000:ℝ) ≤ wfun (x + y) := wc_489 (x + y) (by linarith) (by linarith)
                        have hw5 : (780164241/10000000000000:ℝ) ≤ wfun (x + y + z) := wc_916 (x + y + z) (by linarith) (by linarith)
                        linarith
                      · have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                        have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_45 z (by linarith) (by linarith)
                        have hw3 : (30275949/10000000000000:ℝ) ≤ wfun (x + y) := wc_489 (x + y) (by linarith) (by linarith)
                        have hw4 : (1350713/2500000000000:ℝ) ≤ wfun (y + z) := wc_471 (y + z) (by linarith) (by linarith)
                        have hw5 : (461449393/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_933 (x + y + z) (by linarith) (by linarith)
                        linarith
                    · have hw0 : (433353/5000000000000:ℝ) ≤ wfun x := wc_57 x (by linarith) (by linarith)
                      have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                      have hw2 : (160574441/10000000000000:ℝ) ≤ wfun z := wc_30 z (by linarith) (by linarith)
                      have hw3 : (75190749/10000000000000:ℝ) ≤ wfun (x + y) := wc_498 (x + y) (by linarith) (by linarith)
                      have hw5 : (459679121/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_934 (x + y + z) (by linarith) (by linarith)
                      linarith
                · rcases le_total y (12169/4096:ℝ) with hc | hc
                  · have hw1 : (239478321/1250000000000:ℝ) ≤ wfun y := wc_203 y (by linarith) (by linarith)
                    have hw3 : (163329/5000000000000:ℝ) ≤ wfun (x + y) := wc_463 (x + y) (by linarith) (by linarith)
                    have hw4 : (163329/5000000000000:ℝ) ≤ wfun (y + z) := wc_463 (y + z) (by linarith) (by linarith)
                    have hw5 : (418269633/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_926 (x + y + z) (by linarith) (by linarith)
                    linarith
                  · have hw1 : (136952521/1000000000000:ℝ) ≤ wfun y := wc_207 y (by linarith) (by linarith)
                    have hw3 : (7532357/2500000000000:ℝ) ≤ wfun (x + y) := wc_490 (x + y) (by linarith) (by linarith)
                    have hw4 : (7532357/2500000000000:ℝ) ≤ wfun (y + z) := wc_490 (y + z) (by linarith) (by linarith)
                    have hw5 : (534301079/5000000000000:ℝ) ≤ wfun (x + y + z) := wc_943 (x + y + z) (by linarith) (by linarith)
                    linarith

end Zeta23Ext.Bridge.FourPoint
